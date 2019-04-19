-- 6.823 Lab 3
-- Protocol Framework

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  ProcCount: 3;          -- number processors

  VC0: 0;                -- low priority
  VC1: 1;
  VC2: 2;                -- high priority
  NumVCs: VC2 - VC0 + 1;
  QMax: 2;
  NetMax: 2*ProcCount+1;


----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
type
  Proc: scalarset(ProcCount);   -- unordered range of processors
  Home: enum { HomeType };      -- need enumeration for IsMember calls
  Node: union { Home , Proc };

  VCType: VC0..NumVCs-1;

  -- Message enumeration: you must support the first three, but will need to
  -- add more message types (e.g., various ACKs)
  MessageType: enum {  ShReq,         -- request for shared state
										   ShAck, 
                       ExReq,         -- request for writable state
										   ExAck,
                       WbReq,         -- writeback request (w/ or wo/ data)
											 WbAck,
										   InvReq,        -- request for a processor to invalidate
                       InvAck,
											 DownReq,       -- request for a processor to downgrade from M to S
											 DownAck
                    };

  Message:
    Record
      mtype: MessageType;
      src: Node;
      -- don't need a destination for verification
      vc: VCType;
      aux: Node;  -- participating node (used when forwarding msgs)
      cnt: 0..ProcCount; -- if you need to send an integer count
    End;

  HomeState:
    Record
      -- home node state: you have three stable states (Ex,Sh,Un) but need to
      -- add transient states during races
      state: enum { HEx,			-- State of exclusive ownership
						 				HSh,			-- State of sharing
									 	HUn,			-- State of no use
                    HT_Down,	-- Transition state from Ex -> Sh
										HT_Inv,   -- Transition state from Ex -> U
										HT_Clear  -- Transition state from S -> U
                  };

      owner: Node;
      sharers: multiset [ProcCount] of Node;
      pending_node: Node; -- you may find this useful;
    End;

  ProcState:
    Record
      -- processor state: again, three stable states (M,S,I) but you need to
      state: enum { PM,     -- State of write access
										PS,     -- State of read access
									 	PI,     -- State of invalidity
			              PT_Ex,	-- Transition state getting write permission
										PT_Sh,  -- Transition state getting read permission
                    PT_Wb   -- Transistion state while writeback
                  };
    End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
  HomeNode:  HomeState;
  Procs: array [Proc] of ProcState;
  Net:   array [Node] of multiset [NetMax] of Message;
  msg_processed: boolean;

----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------
Procedure Send(mtype:MessageType;
               dst:Node;
               src:Node;
               vc:VCType;
               aux:Node;            -- See Message above for details of these
               cnt:0..ProcCount     -- args. Pass UNDEFINED if unwanted
               );
var msg:Message;
Begin
  Assert (MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages";
  msg.mtype := mtype;
  msg.src   := src;
  msg.vc    := vc;
  msg.aux   := aux;
  msg.cnt   := cnt;
  MultiSetAdd(msg, Net[dst]);
End;

Procedure ErrorUnhandledMsg(msg:Message; n:Node);
Begin
  switch msg.mtype
  case ExReq, ShReq, WbReq:
    msg_processed := false; 	-- we can receive a raw request any time
  else
    error "Unhandled message type!"; -- or message type that breaks invarients
  endswitch;
End;

Procedure ErrorUnhandledState();
Begin
  error "Unhandled state!";
End;

Procedure AddToSharersList(n:Node);
Begin
  if MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) = 0
  then
    MultiSetAdd(n, HomeNode.sharers);
  end;
End;

Procedure RemoveFromSharersList(n:Node);
Begin
  MultiSetRemovePred(i:HomeNode.sharers, HomeNode.sharers[i] = n);
End;

Procedure SendInvReqToSharers(rqst:Node);
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      if n != rqst
      then
        -- Send invalidation message here
        Send(InvReq, n, HomeType, VC0, n, UNDEFINED);
      end;
    end;
  end;
End;

Procedure HomeReceive(msg:Message);
var cnt:0..ProcCount;
var msg_in_sharers: boolean;
Begin
  -- compiler barfs if we put this inside the switch
  cnt := MultiSetCount(i:HomeNode.sharers, true);
	msg_in_sharers := MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = msg.src) = 1;


  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  switch HomeNode.state
  case HUn:
    Assert (cnt = 0) "Sharers list non-empty, but line is Unshared";

    switch msg.mtype
    case ShReq:
	 		-- ShReq / Sharers = Sharers + {P}; ExResp 
      HomeNode.state := HSh;
      AddToSharersList(msg.src);
      Send(ShAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case ExReq:
			-- ExReq / Sharers = {P}; ExResp
      HomeNode.state := HEx;
      HomeNode.owner := msg.src;
      Send(ExAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HEx:
    Assert (IsUndefined(HomeNode.owner) = false)
       "HomeNode has no owner, but line is Exclusive";

    switch msg.mtype
	  case ExReq:
      -- ExReq / Down(Sharer); Sharer = {P}; ExResp
      HomeNode.state := HT_Inv; 
      Send(InvReq, HomeNode.owner, HomeType, VC0, UNDEFINED, UNDEFINED);
			msg_processed := false;

    case ShReq:
			-- ShReq / Down(Sharer); Sharers = Sharer + {P}; ShResp
      HomeNode.state := HT_Down;
      Send(DownReq, HomeNode.owner, HomeType, VC0, msg.src, UNDEFINED);
    
		case WbReq:
			Assert(HomeNode.owner = msg.src) "Writeback not from owner.";
			HomeNode.state := HUn;
			Send(WbAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);
			undefine HomeNode.owner;

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HSh:
    Assert (cnt != 0) "sharers list empty, but line is shared";

    switch msg.mtype
    case ShReq:
			-- ShReq / Sharers = Sharers + {P}; ShResp
      AddToSharersList(msg.src);
      Send(ShAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);

    case ExReq:
			-- ExReq / Inv(Sharers - {P}); Sharers = {P}; ExResp
      RemoveFromSharersList(msg.src);
	  	if (cnt = 1 & msg_in_sharers)
	  	then
	    	HomeNode.state := HEx;
        HomeNode.owner := msg.src;
      	Send(ExAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);
			else 
      	HomeNode.state := HT_Clear;
      	SendInvReqToSharers(msg.src);
				msg_processed := false;
			end;
    
		case WbReq:
	    RemoveFromSharersList(msg.src);
      Send(WbAck, msg.src, HomeType, VC2, UNDEFINED, UNDEFINED);
	  	if (cnt = 1 & msg_in_sharers)
	  	then
	    	HomeNode.state := HUn;
			end;
			
		else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HT_Clear:
    -- Temporary state used to wait until all sharers have finished invalidating.
    switch msg.mtype
    case InvAck:
      RemoveFromSharersList(msg.src);
      if (cnt = 1 & msg_in_sharers)
      then
        HomeNode.state := HUn;
      end;

		case WbReq:
			-- InvReq already on way.
		  RemoveFromSharersList(msg.src);
	  	if (cnt = 1 & msg_in_sharers)
	  	then
	    	HomeNode.state := HUn;
			end;

    else 
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

	case HT_Down:
    -- Temporary state used to wait to share until owner has finished WB.
    switch msg.mtype
    case WbReq:
			-- DownReq already on way.
			Assert(HomeNode.owner = msg.src) "Writeback not from owner.";
	   	HomeNode.state := HUn;
			undefine HomeNode.owner;

		case DownAck:
			-- msg.aux contains p which sent the ShReq
			AddToSharersList(msg.src);
			AddToSharersList(msg.aux);
			HomeNode.state := HSh;
      undefine HomeNode.owner;

    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

	case HT_Inv:
		-- Temporary state used to wait for owner to invalidate.
		switch msg.mtype
		case InvAck:
      HomeNode.state := HUn;
			undefine HomeNode.owner;

		case WbReq:
			-- InvReq already on way.
			Assert(HomeNode.owner = msg.src) "Writeback not from owner.";
			HomeNode.state := HUn;
			undefine HomeNode.owner;

		else 
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  endswitch;

End;

Procedure ProcReceive(msg:Message; p:Proc);
Begin
  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  alias ps:Procs[p].state do

  switch ps
  case PM:
    switch msg.mtype
    case DownReq:
      ps := PS;
      Send(DownAck, msg.src, p, VC2, msg.aux, UNDEFINED);
			Send(ShAck, msg.aux, p, VC2, UNDEFINED, UNDEFINED);

		case InvReq:
			ps := PI;
			Send(InvAck, msg.src, p, VC0, UNDEFINED, UNDEFINED);

    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PS:
    switch msg.mtype
    case InvReq:
      -- InvReq / InvResp
      ps := PI;
      Send(InvAck, msg.src, p, VC2, UNDEFINED, UNDEFINED);

    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

	case PI:
		-- Should get no messages from the dictionary.
		ErrorUnhandledMsg(msg, p);

  case PT_Sh:
    switch msg.mtype
    case ShAck:
      ps := PS;
    else 
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PT_Ex:
    switch msg.mtype
    case ExAck:
      ps := PM;
		case InvReq:
      Send(InvAck, msg.src, p, VC2, UNDEFINED, UNDEFINED);
    else 
      ErrorUnhandledMsg(msg, p);
    endswitch;

	case PT_Wb:
    switch msg.mtype
    case WbAck, InvReq:
      ps := PI;
		case DownReq:
			ps := PI;
			-- Corner case in which another processor attempted ShReq while 
			-- this processor performed a writeback
			Send(ShReq, msg.src, msg.aux, VC0, UNDEFINED, UNDEFINED);
    else 
      ErrorUnhandledMsg(msg, p);
    endswitch;

  ----------------------------
  -- Error catch
  ----------------------------
  else
    ErrorUnhandledState();

  endswitch;

  endalias;
End;

----------------------------------------------------------------------
-- Rules
----------------------------------------------------------------------

-- Processor actions (affecting coherency)
ruleset n:Proc Do
  alias p:Procs[n] Do

  rule "read request"
    p.state = PI
  ==>
    p.state := PT_Sh;
    Send(ShReq, HomeType, n, VC0, UNDEFINED, UNDEFINED);
  endrule;

  rule "write request"
    (p.state = PI)
  ==>
    p.state := PT_Ex;
    Send(ExReq, HomeType, n, VC0, UNDEFINED, UNDEFINED);
  endrule;

  rule "upgrade request"
    (p.state = PS)
  ==>
    p.state := PT_Ex;
    Send(ExReq, HomeType, n, VC0, UNDEFINED, UNDEFINED);
  endrule;

  rule "writeback"
    (p.state = PM)
  ==>
    p.state := PT_Wb;
    Send(WbReq, HomeType, n, VC0, UNDEFINED, UNDEFINED);
  endrule;

  rule "evict"
    (p.state = PS)
  ==>
    p.state := PT_Wb;
    Send(WbReq, HomeType, n, VC0, UNDEFINED, UNDEFINED);
  endrule;

  endalias;
endruleset;

-- receive rules
ruleset n:Node do
  choose midx:Net[n] do
    alias chan:Net[n] do
    alias msg:chan[midx] do

    rule "receive"
      (msg.vc = VC2) |
      (msg.vc = VC1 & MultiSetCount(m:chan, chan[m].vc = VC2)  = 0) |
      (msg.vc = VC0 & MultiSetCount(m:chan, chan[m].vc = VC2)  = 0
                    & MultiSetCount(m:chan, chan[m].vc = VC1)  = 0)
    ==>

      if IsMember(n, Home)
      then
        HomeReceive(msg);

        if msg_processed
        then
          MultiSetRemove(midx, chan);
        end;

      else
        ProcReceive(msg, n);

        if msg_processed
        then
          MultiSetRemove(midx, chan);
        end;

      end;

    endrule;

    endalias;
    endalias;
  endchoose;
endruleset;

----------------------------------------------------------------------
-- Startstate
----------------------------------------------------------------------
startstate

  -- home node initialization
  HomeNode.state := HUn;
  undefine HomeNode.sharers;
  undefine HomeNode.owner;
  undefine HomeNode.pending_node;

  -- processor initialization
  for i:Proc do
    Procs[i].state := PI;
  end;

  -- network initialization
  undefine Net;
endstartstate;

----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------

invariant "exclusive w/ empty sharers list"
  HomeNode.state = HEx
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "unshared implies empty owner"
  HomeNode.state = HUn
    ->
      IsUndefined(HomeNode.owner);

invariant "unshared implies empty sharer list"
  HomeNode.state = HUn
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "exclusive implies no sharing processors"
  forall n : Proc do
    (HomeNode.state = HEx)
      ->
        (Procs[n].state != PS)
  end;

invariant "shared implies no processor in modified"
  forall n : Proc do
    (HomeNode.state = HSh)
      ->
        (Procs[n].state != PM)
  end;
