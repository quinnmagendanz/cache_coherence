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
                       InvResp,
                       DownReq,
                       DownResp
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
			        HTPend 
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
			        PPend
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
  case WriteReq, ReadReq, WBReq:
    msg_processed := false;  -- we can receive a raw request any time
  else
    error "Unhandled message type!";
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
        Send(InvReq, HomeNode, n, VC0, UNDEFINED, UNDEFINED);
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
      Send(ShResp, HomeNode, msg.src, VC0, UNDEFINED, UNDEFINED);

    case ExReq:
      -- TODO: perform actions here!
			-- ExReq / Sharers = {P}; ExResp
      HomeNode.state := HEx;
      HomeNode.owner := msg.src;
      Send(ExResp, HomeNode, msg.src, VC0, UNDEFINED, UNDEFINED);

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HEx:
    Assert (IsUndefined(HomeNode.owner) = false)
       "HomeNode has no owner, but line is Exclusive";

    switch msg.mtype

    case ShReq:
      -- TODO: perform actions here!
			-- ShReq / Down(Sharer); Sharers = Sharer + {P}; ShResp
      HomeNode.state := ESh;
      AddToSharersList(msg.src);
      Send(DownReq, HomeNode, HomeNode.owner, VC0, UNDEFINED, UNDEFINED);
      Send(ShResp, HomeNode, msg.src, VC0, UNDEFINED, UNDEFINED);
      undefine HomeNode.owner;

    case WbReq:
      -- TODO: perform actions here!
			-- WbReq / Sharers = {}; WbResp
      HomeNode.state := EUn;
      undefine HomeNode.owner;
      Send(WbResp, HomeNode, msg.src, VC0, UNDEFINED, UNDEFINED);

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  case HSh:
    Assert (cnt != 0) "sharers list empty, but line is shared";

    switch msg.mtype

    case ShReq:
      -- TODO: perform actions here!
			-- ShReq / Sharers = Sharers + {P}; ShResp
      AddiToSharersList(msg.src);
      Send(ShResp, HomeType, n, VC0, UNDEFINED, UNDEFINED);

    case ExReq:
      -- TODO: perform actions here!
			-- ExReq / Inv(Sharers - {P}); Sharers = {P}; ExResp
      RemoveFromSharersList(msg.src);
      SendInvReqToSharers(msg.src);
      HomeNode.owner = msg.src;

    case WbReq:
      -- WbReq && |Sharers| > 1 / Sharers = Sharers - {P}; WbResp
      -- WbReq && |Sharers| == 1 / Sharers = {}; WbResp
      RemoveFromSharersList(msg.src);
      if MultiSetCount(i:HomeNode.sharers, true) = 0
      then
        HomeNode.state := HUn;
      end
      Send(WBResp, HomeType, n, VC0, UNDEFINED, UNDEFINED);

    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;

  -- TODO: add other cases from home node state here!
  -- TODO(magendanz) InvAck

  endswitch;

End;

Procedure ProcReceive(msg:Message; p:Proc);
Begin
  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  alias ps:Procs[p].state do

  switch ps
  case PI:

    switch msg.mtype
      -- TODO: handle message cases here!
    case ShResp:


    case ExResp:
    

    case WbResp:


    case InvReq:


    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PM:

    switch msg.mtype
      -- TODO: handle message cases here!
    case ShResp:


    case ExResp:
    

    case WbResp:


    case InvReq:
      -- InvReq / InvResp(data)

    case DownReq:
      -- DownReq / DownResp(data)

    else
      ErrorUnhandledMsg(msg, p);
    endswitch;

  case PS:

    switch msg.mtype
      -- TODO: handle message cases here!
    case ShResp:


    case ExResp:
    

    case WbResp:


    case InvReq:
      -- InvReq / InvResp

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
    Send(ReadReq, HomeType, n, VC0, UNDEFINED, UNDEFINED);
    -- TODO: any other actions?
  endrule;

  rule "write request"
    (p.state = PI)
  ==>
    Send(WriteReq, HomeType, n, VC0, UNDEFINED, UNDEFINED);
    -- TODO: any other actions?
  endrule;

  rule "upgrade request"
    (p.state = PS)
  ==>
    Send(WriteReq, HomeType, n, VC0, UNDEFINED, UNDEFINED);
    -- TODO: any other actions?
  endrule;

  rule "writeback"
    (p.state = PM)
  ==>
    Send(WBReq, HomeType, n, VC0, UNDEFINED, UNDEFINED);
    -- TODO: any other actions?
  endrule;

  rule "evict"
    (p.state = PS)
  ==>
    p.state := PI;
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
