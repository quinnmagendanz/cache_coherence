-- 6.823 Lab 3
-- Protocol Framework

-- See the lines marked TODO in file below. Try adding support for just a read
-- request first (comment out other starting rules).

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  -- TODO: start with this number at 1, then increase to 2 and eventually 3
  ProcCount: 2;          -- number processors

  VC0: 0;                -- low priority
  VC1: 1;
  VC2: 2;                -- high priority
  NumVCs: VC2 - VC0 + 1;
  QMax: 2;
  NetMax: ProcCount+3;


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
                       ExReq,         -- write request
                       WbReq,         -- writeback request (w/ or wo/ data)
                       -- TODO: add more messages here!
										   ShAck,
										   ExAck,
										   InvReq,
                       InvAck,
											 InvDone,
											 DownReq,
											 DownAck,
											 WbAck,
											 DownDone
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
      state: enum { HEx, HSh, HUn,
			 		          -- TODO: add transient states here!
			              HT_Ex,
                    HT_Down,
										HT_Wb,
										HT_Inv,
										HT_Clear
                  };

      owner: Node;
      sharers: multiset [ProcCount] of Node;
      pending_node: Node; -- you may find this useful;
      -- TODO add other variables if needed
    End;

  ProcState:
    Record
      -- processor state: again, three stable states (M,S,I) but you need to
      -- TODO add transient states to support races
      state: enum { PM, PS, PI,
			              PT_Ex,
										PT_Sh,
										PT_Down,
                    PT_Wb,
										PT_Inv
                  };

      -- TODO add other variables if needed
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
  case ExReq, ShReq, InvAck, DownAck:
    msg_processed := false; 	-- we can receive a raw request any time
															-- or we need to push off an Ack until in correct state
	case DownReq, InvReq:
		-- Drop DownReqs and InvReqs that are recieved when we are not in HEx or HSh.
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
        Send(InvAck, n, HomeType, VC0, UNDEFINED, UNDEFINED);
      end;
    end;
  end;
End;

Procedure HomeReceive(msg:Message);
var cnt:0..ProcCount;
var msg_in: boolean;
Begin
  -- compiler barfs if we put this inside the switch
  cnt := MultiSetCount(i:HomeNode.sharers, true);
  msg_in := MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = msg.src) = 1;

  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  switch HomeNode.state
  case HUn:
    Assert (cnt = 0) "Sharers list non-empty, but line is Unshared";

    switch msg.mtype
    case ShReq:
      -- TODO: perform actions here!
	 		-- ShReq / Sharers = Sharers + {P}; ExResp 
      HomeNode.state := HSh;
      AddToSharersList(msg.src);
      Send(ShAck, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED);

    case ExReq:
      -- TODO: perform actions here!
			-- ExReq / Sharers = {P}; ExResp
      HomeNode.state := HEx;
      HomeNode.owner := msg.src;
      Send(ExAck, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED);

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HEx:
    Assert (IsUndefined(HomeNode.owner) = false)
       "HomeNode has no owner, but line is Exclusive";

    switch msg.mtype
	  case ExReq:
      -- ExReq / Down(Sharer); Sharer = {P}; ExResp
	  	-- TODO(magendanz) add case where is current owner
      HomeNode.state := HT_Ex; 
      Send(DownAck, HomeNode.owner, HomeType, VC0, UNDEFINED, UNDEFINED);
      HomeNode.owner := msg.src;

    case ShReq:
      -- TODO: perform actions here!
			-- ShReq / Down(Sharer); Sharers = Sharer + {P}; ShResp
      HomeNode.state := HT_Down;
      Send(DownAck, HomeNode.owner, HomeType, VC0, UNDEFINED, UNDEFINED);
      HomeNode.owner := msg.src;  -- Temporarily make ShReq node owner. 
      
    case DownReq:
      -- TODO: perform actions here!
			-- WbReq / Sharers = {}; WbResp
			if HomeNode.owner = msg.src
			then
     		HomeNode.state := HT_Wb;
     		undefine HomeNode.owner;
     		Send(DownAck, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED);
			end; -- Drop old WbReqs from former, different owners

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HSh:
    Assert (cnt != 0) "sharers list empty, but line is shared";

    switch msg.mtype
    case ShReq:
      -- TODO: perform actions here!
			-- ShReq / Sharers = Sharers + {P}; ShResp
      -- TODO(magendanz) add case where already sharer
      AddToSharersList(msg.src);
      Send(ShAck, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED);

    case ExReq:
      -- TODO: perform actions here!
			-- ExReq / Inv(Sharers - {P}); Sharers = {P}; ExResp
      RemoveFromSharersList(msg.src);
      HomeNode.owner := msg.src;
	  	if (msg_in & cnt = 1)
	  	then
	    	HomeNode.state := HEx;
      	Send(ExAck, HomeNode.owner, HomeType, VC0, UNDEFINED, UNDEFINED);
			else 
      	HomeNode.state := HT_Clear;
      	SendInvReqToSharers(msg.src);
			end;

    case InvReq:
      -- WbReq && |Sharers| > 1 / Sharers = Sharers - {P}; WbResp
      -- WbReq && |Sharers| == 1 / Sharers = {}; WbResp
			if msg_in
			then
				HomeNode.state := HT_Inv;
      	RemoveFromSharersList(msg.src);
      	Send(InvAck, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED);
			end;

    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case HT_Clear:
    -- Temporary state used to wait until all sharers have finished invalidating.
    switch msg.mtype
    case InvDone:
	  	-- Remove the sharer who responded to the invalidation request
      RemoveFromSharersList(msg.src);
	  	-- Move to next state if there were no sharers or last sharer removed
      if cnt = 0 | cnt = 1
      then
        HomeNode.state := HEx;
        Send(ExAck, HomeNode.owner, HomeType, VC0, UNDEFINED, UNDEFINED);
      end;
    else 
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

	case HT_Down:
    -- Temporary state used to wait to share until owner has finished WB.
    switch msg.mtype
    case WbReq:
      Send(WbAck, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED);
		case DownDone:
      -- Note that temporary owner is node that made ShReq.
      -- Previous owner has just sent the WbReq.
			Send(ShAck, HomeNode.owner, HomeType, VC0, UNDEFINED, UNDEFINED);
			AddToSharersList(HomeNode.owner);
      undefine HomeNode.owner;
			HomeNode.state := HSh;
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

	case HT_Wb:
		-- Temporary state used to wait to release until owner has finished WB.
		switch msg.mtype
		case WbReq:
      Send(WbAck, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED);
		case DownDone:
			HomeNode.state := HUn;
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

	case HT_Ex:
		-- Temporary state used to wait to change owner until owner has finished WB.
  	switch msg.mtype
		case WbReq:
      Send(WbAck, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED);
		case DownDone:
      Send(ExAck, HomeNode.owner, HomeType, VC0, UNDEFINED, UNDEFINED);
			HomeNode.state := HEx;
		else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

	case HT_Inv:
		-- Temporary state used to wait for sharer to invalidate.
		switch msg.mtype
		case InvDone:
   		if cnt = 0
      then
        HomeNode.state := HUn;
			else 
				HomeNode.state := HSh;
      end;
		else 
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  -- TODO: add other cases from home node state here!
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
    -- TODO: handle message cases here!
    case DownAck:
      ps := PT_Wb;
      Send(WbReq, msg.src, p, VC0, UNDEFINED, UNDEFINED);

    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PS:
    switch msg.mtype
      -- TODO: handle message cases here!
    case InvAck:
      -- InvReq / InvResp
      ps := PI;
      Send(InvDone, msg.src, p, VC0, UNDEFINED, UNDEFINED);

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
		case InvAck:
      Send(InvDone, msg.src, p, VC0, UNDEFINED, UNDEFINED);
    else 
      ErrorUnhandledMsg(msg, p);
    endswitch;

 	case PT_Down:
		switch msg.mtype
		case DownAck:
			ps := PT_Wb;
      Send(WbReq, msg.src, p, VC0, UNDEFINED, UNDEFINED);
		else 
      ErrorUnhandledMsg(msg, p);
    endswitch;
	 
	case PT_Wb:
    switch msg.mtype
    case WbAck:
      ps := PI;
      Send(DownDone, msg.src, p, VC0, UNDEFINED, UNDEFINED);
    else 
      ErrorUnhandledMsg(msg, p);
    endswitch;

	case PT_Inv:
		switch msg.mtype
		case InvAck:
			ps := PI;
      Send(InvDone, msg.src, p, VC0, UNDEFINED, UNDEFINED);
		else
			ErrorUnhandledMsg(msg, p);
		endswitch;

 -- TODO: add additional states from Proc here!

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
    -- TODO: any other actions?
  endrule;

  rule "write request"
    (p.state = PI)
  ==>
    p.state := PT_Ex;
    Send(ExReq, HomeType, n, VC0, UNDEFINED, UNDEFINED);
    -- TODO: any other actions?
  endrule;

  rule "upgrade request"
    (p.state = PS)
  ==>
    p.state := PT_Ex;
    Send(ExReq, HomeType, n, VC0, UNDEFINED, UNDEFINED);
    -- TODO: any other actions?
  endrule;

  rule "writeback"
    (p.state = PM)
  ==>
    p.state := PT_Down;
    Send(DownReq, HomeType, n, VC0, UNDEFINED, UNDEFINED);
    -- TODO: any other actions?
  endrule;

  rule "evict"
    (p.state = PS)
  ==>
    p.state := PT_Inv;
    Send(InvReq, HomeType, n, VC0, UNDEFINED, UNDEFINED);
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
    -- TODO: any other initialization?
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
