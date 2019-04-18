-- 6.823 Lab 3
-- Protocol Framework

-- See the lines marked TODO in file below. Try adding support for just a read
-- request first (comment out other starting rules).

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  -- TODO: start with this number at 1, then increase to 2 and eventually 3
  ProcCount: 1;          -- number processors

  VC0: 0;                -- low priority
  VC1: 1;
  VC2: 2;                -- high priority
  NumVCs: VC2 - VC0 + 1;
  QMax: 2;
  NetMax: ProcCount+1;


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
										   ShResp,
										   ExResp,
										   WbResp,
										   InvReq,
                       -- InvResp = WbReq
                       DownReq
                       -- DownResp = WbReq
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
			              HT_Down,
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
                    PT_Wb
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
  case ExReq, ShReq, WbReq:
    msg_processed := false;  -- we can receive a raw request any time
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
        Send(InvReq, n, HomeType, VC0, UNDEFINED, UNDEFINED);
      end;
    end;
  end;
End;

Procedure HomeReceive(msg:Message);
var cnt:0..ProcCount;
Begin
  -- compiler barfs if we put this inside the switch
  cnt := MultiSetCount(i:HomeNode.sharers, true);

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
      Send(ShResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED);

    case ExReq:
      -- TODO: perform actions here!
			-- ExReq / Sharers = {P}; ExResp
      HomeNode.state := HEx;
      HomeNode.owner := msg.src;
      Send(ExResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED);

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HEx:
    Assert (IsUndefined(HomeNode.owner) = false)
       "HomeNode has no owner, but line is Exclusive";

    switch msg.mtype

	  case ExReq:
      -- ExReq / Down(Sharer); Sharer = {P}; ExResp
      HomeNode.state := HT_Clear; 
      Send(DownReq, HomeNode.owner, HomeType, VC0, UNDEFINED, UNDEFINED);
      HomeNode.owner := msg.src;

    case ShReq:
      -- TODO: perform actions here!
			-- ShReq / Down(Sharer); Sharers = Sharer + {P}; ShResp
      HomeNode.state := HT_Down;
      Send(DownReq, HomeNode.owner, HomeType, VC0, UNDEFINED, UNDEFINED);
      HomeNode.owner := msg.src;  -- Temporarily make ShReq node owner. 
      
    case WbReq:
      -- TODO: perform actions here!
			-- WbReq / Sharers = {}; WbResp
      Assert (HomeNode.owner = msg.src) "Non-owner writing";
      HomeNode.state := HUn;
      undefine HomeNode.owner;
      Send(WbResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED);

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HSh:
    Assert (cnt != 0) "sharers list empty, but line is shared";

    switch msg.mtype

    case ShReq:
      -- TODO: perform actions here!
			-- ShReq / Sharers = Sharers + {P}; ShResp
      AddToSharersList(msg.src);
      Send(ShResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED);

    case ExReq:
      -- TODO: perform actions here!
			-- ExReq / Inv(Sharers - {P}); Sharers = {P}; ExResp
      RemoveFromSharersList(msg.src);
      HomeNode.owner := msg.src;
	  	if cnt > 1
	  	then
      	HomeNode.state := HT_Clear;
      	SendInvReqToSharers(msg.src);
			else
	    	HomeNode.state := HEx;
      	Send(ExResp, HomeNode.owner, HomeType, VC0, UNDEFINED, UNDEFINED);
			end;

    case WbReq:
      -- WbReq && |Sharers| > 1 / Sharers = Sharers - {P}; WbResp
      -- WbReq && |Sharers| == 1 / Sharers = {}; WbResp
      if cnt = 1
      then
        HomeNode.state := HUn;
      end;
      RemoveFromSharersList(msg.src);
      Send(WbResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED);

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HT_Down:
    -- Temporary state used to wait until owner has ACKed Down.
    switch msg.mtype
   
    case WbReq:
      -- Note that temporary owner is node that made ShReq.
      -- Previous owner has just sent the WbReq.
      AddToSharersList(HomeNode.owner);
      Send(ShResp, HomeNode.owner, HomeType, VC0, UNDEFINED, UNDEFINED);
      undefine HomeNode.owner;

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HT_Clear:
    -- Temporary state used to wait until all sharers have ACKed invalidated.
    switch msg.mtype

    case WbReq:
	  -- Remove the sharer who responded to the invalidation request
      if cnt >= 1
      then 
        RemoveFromSharersList(msg.src);
        Send(WbResp, msg.src, HomeType, VC0, UNDEFINED, UNDEFINED);
      end;
	  -- Move to next state if there were no sharers or last sharer removed
      if cnt = 0 | cnt = 1
      then
        HomeNode.state := HEx;
        Send(ExResp, HomeNode.owner, HomeType, VC0, UNDEFINED, UNDEFINED);
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
    case DownReq:
      ps := PT_Wb;
      Send(WbReq, msg.src, p, VC1, UNDEFINED, UNDEFINED);

    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PS:

    switch msg.mtype
      -- TODO: handle message cases here!

    case InvReq:
      -- InvReq / InvResp
      ps := PT_Wb;
      Send(WbReq, msg.src, p, VC1, UNDEFINED, UNDEFINED);

    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PT_Sh:

    switch msg.mtype

    case ShResp:
      ps := PS;

    else 
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PT_Ex:

    switch msg.mtype

    case ExResp:
      ps := PM;

    else 
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PT_Wb:
    switch msg.mtype

    case WbResp:
      ps := PI;

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
    p.state := PT_Wb;
    Send(WbReq, HomeType, n, VC0, UNDEFINED, UNDEFINED);
    -- TODO: any other actions?
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
