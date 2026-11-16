import Base
import ../shared/owner_groups/spec.bend as OwnerGroups
import ../shared/record_views/spec.bend as RecordViews
import ../shared/shared/record_sync/spec.bend as RecordSync
import ../shared/shared/shared/monotone_queries/spec.bend as MonotoneQueries
import ../shared/shared/shared/shared/part_store/spec.bend as PartStore
import ../shared/shared/shared/shared/shared/sha256/spec.bend as Sha256
import ../shared/shared/shared/shared/shared/shared/shared.bend as Shared
import ../shared/shared/shared/shared/shared/word_list_sets/spec.bend as WordListSets
import ../shared/shared/shared/shared/signatures/spec.bend as Signatures
import ../shared/shared/shared/signed_records/spec.bend as SignedRecords
import ../shared/shared/slot_consensus/spec.bend as SlotConsensus

# A node is one pure step: its state and one deed give its next state and what
# it outputs. The IO around it only reads deeds (from clients, peers and the
# clock) and performs outputs (persisting, sending, replying, fetching); every
# other part of the program is here.
#
# Hooks, given by the application on top (Vend):
# - ballot_of and ballot_body: how a ballot is written as the words of a record;
# - claim_of and claim_body: the same for a claim to keep a part;
# - decode and encode_choice: how a decided choice says its era (owner groups);
# - plan: the steps to work on, each with the payload to propose;
# - needed: the parts that the node needs;
# - answer: the answer to a client's question.

# what a node is set up with: the root line and the changes that start it, the
# trusted keepers of parts, and how many of them must keep a part before a node
# may drop it
type NodeConfig is Data:
  NodeConfig{
    root: List<&2, U32>,
    genesis: List<&2, OwnerGroups.GroupChange>,
    keepers: List<&2, List<&2, U32>>,
    copies: Nat
  }

# what happens to a node
type Deed is Data:
  ClientConnects{client: List<&2, U32>}
  ClientLeaves{client: List<&2, U32>}
  ClientSubmits{
    client: List<&2, U32>,
    record: SignedRecords.SignedRecord,
    contents: List<&2, List<&2, U32>>
  }
  ClientAsks{client: List<&2, U32>, question: List<&2, U32>}
  PeerOpensSync{peer: List<&2, U32>}
  PeerSyncMessage{peer: List<&2, U32>, message: List<&2, U32>}
  PeerAsksParts{peer: List<&2, U32>, message: List<&2, U32>}
  PeerAnswersParts{message: List<&2, U32>}
  TimerTicks{}
  NodeWorks{}
  StopAsked{force: Bool}

# Connect, Leave: a client connects or leaves (a mounted resource is a client).
# Submit: a client hands in a record that its author signed, with the parts of
# content that it carries. Ask: a client asks a question. SyncOpen,
# SyncMessage: a sync starts with a peer, or a peer's sync message arrives.
# PartAsk, PartAnswer: a peer asks for parts, or answers this node's ask. Tick:
# the round timer ran out. Work: the node casts its ballots, claims the parts
# it keeps, drops what it may, and asks for the parts it lacks. Stop: the node
# is asked to stop.

# what a node does outside itself
type Output is Data:
  PersistRecord{record: SignedRecords.SignedRecord}
  PersistPart{part: List<&2, U32>}
  SendSync{peer: List<&2, U32>, message: List<&2, U32>}
  SendParts{peer: List<&2, U32>, message: List<&2, U32>}
  FetchParts{parts: List<&2, Shared.FixedLengthList(U32, 8n)>}
  ReplyToClient{client: List<&2, U32>, answer: List<&2, U32>}

# Persist, PersistPart: write a new record or part to storage, before any
# message goes out. Send, SendPart: a sync or part message to a peer. Fetch:
# ask some peer for these parts. Reply: answer a client.

# a node: its signer (never copied, so a node never signs twice from one
# state), its name (its public key), its records and parts, its clients, and
# whether it stopped
type NodeState is Type:
  NodeState{
    signer: Signatures.Signer,
    name: List<&2, U32>,
    records: SignedRecords.SignedRecordSet(),
    parts: PartStore.PartStore,
    clients: List<&2, List<&2, U32>>,
    stopped: Bool
  }

# the name of the node st
def NodeState.name(st: NodeState) -> List<&2, U32>:
  match st:
    case NodeState{sg, n, rs, ps, cs, x}:
      n

# the records of the node st
def NodeState.records(st: NodeState) -> SignedRecords.SignedRecordSet():
  match st:
    case NodeState{sg, n, rs, ps, cs, x}:
      rs

# the parts of the node st
def NodeState.parts(st: NodeState) -> PartStore.PartStore:
  match st:
    case NodeState{sg, n, rs, ps, cs, x}:
      ps

# the clients of the node st
def NodeState.clients(st: NodeState) -> List<&2, List<&2, U32>>:
  match st:
    case NodeState{sg, n, rs, ps, cs, x}:
      cs

# the trusted keepers of config
def NodeConfig.keepers(config: NodeConfig) -> List<&2, List<&2, U32>>:
  match config:
    case NodeConfig{root, genesis, ks, n}:
      ks

# how many keepers must keep a part before a node of config may drop it
def NodeConfig.copies(config: NodeConfig) -> Nat:
  match config:
    case NodeConfig{root, genesis, ks, n}:
      n

# the node st has stopped
def NodeState.stopped(st: NodeState) -> Bool:
  match st:
    case NodeState{sg, n, rs, ps, cs, x}:
      x

# the signer of the node st
def NodeState.signer(st: NodeState) -> Signatures.Signer:
  match st:
    case NodeState{sg, n, rs, ps, cs, x}:
      sg

# The step
# --------

# a new node, of the signer signer: no record, no part, no client
law Node.start:
  for ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>
  for ~ballot_body: RecordViews.BallotBody -> List<&2, U32>
  for ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>
  for ~claim_body: Shared.FixedLengthList(U32, 8n) -> List<&2, U32>
  for ~decode: List<&2, U32> -> OwnerGroups.DecodedChoice
  for ~encode_choice: Nat -> List<&2, U32> -> List<&2, U32>
  for ~plan: SignedRecords.SignedRecordSet() -> List<
    &2,
    +Sigma<SlotConsensus.Step, _ => List<&2, U32>>>
  for ~needed: SignedRecords.SignedRecordSet() -> List<&2, Shared.FixedLengthList(U32, 8n)>
  for ~answer: SignedRecords.SignedRecordSet() -> PartStore.PartStore -> List<
    &2,
    U32> -> List<&2, U32>
  for config: NodeConfig
  for signer: Signatures.Signer
  NodeState

# the node of the signer signer, resumed from the records and parts that it
# persisted, if they are sound: every record checks, and its own ballots
# contradict none of its own
law Node.resume:
  for ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>
  for ~ballot_body: RecordViews.BallotBody -> List<&2, U32>
  for ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>
  for ~claim_body: Shared.FixedLengthList(U32, 8n) -> List<&2, U32>
  for ~decode: List<&2, U32> -> OwnerGroups.DecodedChoice
  for ~encode_choice: Nat -> List<&2, U32> -> List<&2, U32>
  for ~plan: SignedRecords.SignedRecordSet() -> List<
    &2,
    +Sigma<SlotConsensus.Step, _ => List<&2, U32>>>
  for ~needed: SignedRecords.SignedRecordSet() -> List<&2, Shared.FixedLengthList(U32, 8n)>
  for ~answer: SignedRecords.SignedRecordSet() -> PartStore.PartStore -> List<
    &2,
    U32> -> List<&2, U32>
  for config: NodeConfig
  for signer: Signatures.Signer
  for records: List<&2, SignedRecords.SignedRecord>
  for contents: List<&2, List<&2, U32>>
  Maybe<&1, NodeState>

# the node st after the deed d, and what it outputs
law Node.step:
  for ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>
  for ~ballot_body: RecordViews.BallotBody -> List<&2, U32>
  for ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>
  for ~claim_body: Shared.FixedLengthList(U32, 8n) -> List<&2, U32>
  for ~decode: List<&2, U32> -> OwnerGroups.DecodedChoice
  for ~encode_choice: Nat -> List<&2, U32> -> List<&2, U32>
  for ~plan: SignedRecords.SignedRecordSet() -> List<
    &2,
    +Sigma<SlotConsensus.Step, _ => List<&2, U32>>>
  for ~needed: SignedRecords.SignedRecordSet() -> List<&2, Shared.FixedLengthList(U32, 8n)>
  for ~answer: SignedRecords.SignedRecordSet() -> PartStore.PartStore -> List<
    &2,
    U32> -> List<&2, U32>
  for config: NodeConfig
  for st: NodeState
  for d: Deed
  NodeState & List<&2, Output>

# Contracts of the hooks
# ----------------------

# ballot_of reads back what ballot_body writes
def BallotCodec(
  ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>,
  ~ballot_body: RecordViews.BallotBody -> List<&2, U32>
) -> Type:
  @b: RecordViews.BallotBody -> {
    ballot_of(ballot_body(b)) == Some{b}: Maybe<&2, RecordViews.BallotBody>
  }

# claim_of reads back what claim_body writes
def ClaimCodec(
  ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>,
  ~claim_body: Shared.FixedLengthList(U32, 8n) -> List<&2, U32>
) -> Type:
  @h: Shared.FixedLengthList(
    U32,
    8n
  ) -> {claim_of(claim_body(h)) == Some{h}: Maybe<&2, Shared.FixedLengthList(U32, 8n)>}

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- said only in laws: no code that runs calls these readers of a node, its outputs or its plan, so what they compute in excess costs nothing
# Reading a node
# --------------

# the record set rs holds the key k of a record whose author is v
def AuthoredBy(rs: SignedRecords.SignedRecordSet(), k: List<&2, U32>, v: List<&2, U32>) -> Type:
  SignedRecords.Has(
    rs,
    k
  )
    & Exists(
      Shared.FixedLengthList(U32, 8n),
      au => Exists(
        List<&2, U32>,
        bo => Exists(
          List<&2, U32>,
          sg => {
            SignedRecords.SignedRecord.from_key(
              k
            )
              == Some{SignedRecords.SignedRecord{au, bo, sg}}: Maybe<&2, SignedRecords.SignedRecord>
          }
            & {Shared.FixedLengthList.to_list(U32, 8n, au) == v: List<&2, U32>}
        )
      )
    )

# no two ballots of the voter me among the records rs contradict each other
def NoOwnContradiction(
  ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>,
  rs: SignedRecords.SignedRecordSet(),
  me: List<&2, U32>
) -> Type:
  @a: SlotConsensus.Ballot -> @b: SlotConsensus.Ballot
    -> {
      List.contains(
        ~SlotConsensus.Ballot,
        ~SlotConsensus.Ballot.same,
        RecordViews.RecordViews.ballots(~ballot_of, rs),
        a
      )
        == True{}: Bool
    }
    -> {
      List.contains(
        ~SlotConsensus.Ballot,
        ~SlotConsensus.Ballot.same,
        RecordViews.RecordViews.ballots(~ballot_of, rs),
        b
      )
        == True{}: Bool
    }
    -> {SlotConsensus.Ballot.voter(a) == me: List<&2, U32>}
    -> {SlotConsensus.Ballot.contradicts(a, b) == False{}: Bool}

# what holds of every node: its records all check, its own ballots contradict
# none of its own, and its name is its signer's public key
def Invariant(
  ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>,
  st: NodeState
) -> Type:
  SignedRecords.OnlyChecked(
    NodeState.records(st)
  )
    & (
      NoOwnContradiction(
        ~ballot_of,
        NodeState.records(st),
        NodeState.name(st)
      )
        & {
          NodeState.name(
            st
          )
            == Shared.FixedLengthList.to_list(
              U32,
              8n,
              Pair.fst(
                Shared.FixedLengthList(U32, 8n),
                Signatures.Signer,
                Signatures.Signer.public_key(NodeState.signer(st))
              )
            ): List<&2, U32>
        }
    )

# one of the records rs has the key k
def KeyIn(rs: List<&2, SignedRecords.SignedRecord>, k: List<&2, U32>) -> Type:
  match rs:
    case Nil{}:
      Empty
    case Con{r, rest}:
      {SignedRecords.SignedRecord.key(r) == k: List<&2, U32>} | KeyIn(rest, k)

# the outputs os persist a record whose key is k
def PersistsKey(os: List<&2, Output>, k: List<&2, U32>) -> Type:
  match os:
    case Nil{}:
      Empty
    case Con{PersistRecord{r}, rest}:
      {SignedRecords.SignedRecord.key(r) == k: List<&2, U32>} | PersistsKey(rest, k)
    case Con{o, rest}:
      PersistsKey(rest, k)

# the outputs os persist a part whose hash is h
def PersistsPart(os: List<&2, Output>, h: Shared.FixedLengthList(U32, 8n)) -> Type:
  match os:
    case Nil{}:
      Empty
    case Con{PersistPart{ws}, rest}:
      {Sha256.Sha256.of_words(ws) == h: Shared.FixedLengthList(U32, 8n)} | PersistsPart(rest, h)
    case Con{o, rest}:
      PersistsPart(rest, h)

# o persists something
def Output.persists(o: Output) -> Bool:
  match o:
    case PersistRecord{r}:
      True{}
    case PersistPart{ws}:
      True{}
    case _:
      False{}

# no output of os persists
def Outputs.none_persist(os: List<&2, Output>) -> Bool:
  match os:
    case Nil{}:
      True{}
    case Con{o, rest}:
      Bool.and(Bool.not(Output.persists(o)), Outputs.none_persist(rest))

# every output of os that persists comes before every output that does not
def Outputs.persist_first(os: List<&2, Output>) -> Bool:
  match os:
    case Nil{}:
      True{}
    case Con{o, +rest}:
      Bool.pick(Bool, Output.persists(o), Outputs.persist_first(rest), Outputs.none_persist(rest))

# the clients after the deed d, from cs
def Deed.clients(d: Deed, cs: List<&2, List<&2, U32>>) -> List<&2, List<&2, U32>>:
  match d:
    case ClientConnects{+c}:
      c <> PartStore.others(cs, c)
    case ClientLeaves{c}:
      PartStore.others(cs, c)
    case _:
      cs

# whether a node has stopped after the deed d: it had, or d is a stop that is
# forced or finds no client
def Deed.stopped(d: Deed, s: Bool, cs: List<&2, List<&2, U32>>) -> Bool:
  match d:
    case StopAsked{f}:
      Bool.or(s, Bool.or(f, List.is_empty(&2, List<&2, U32>, cs)))
    case _:
      s

# the deed d changes no record of a node: it brings no record in and signs none
def Deed.keeps_records(d: Deed) -> Bool:
  match d:
    case ClientConnects{c}:
      True{}
    case ClientLeaves{c}:
      True{}
    case ClientAsks{c, q}:
      True{}
    case PeerOpensSync{p}:
      True{}
    case PeerAsksParts{p, m}:
      True{}
    case PeerAnswersParts{m}:
      True{}
    case StopAsked{f}:
      True{}
    case _:
      False{}

# the deed d changes no part of a node: it brings no part in and drops none
def Deed.keeps_parts(d: Deed) -> Bool:
  match d:
    case ClientSubmits{c, r, cs}:
      False{}
    case PeerAnswersParts{m}:
      False{}
    case NodeWorks{}:
      False{}
    case _:
      True{}

# the author of the record r, as words
def author_of(r: SignedRecords.SignedRecord) -> List<&2, U32>:
  match r:
    case SignedRecords.SignedRecord{au, bo, sg}:
      Shared.FixedLengthList.to_list(U32, 8n, au)

# the outputs of os that do not persist
def Outputs.messages(os: List<&2, Output>) -> List<&2, Output>:
  match os:
    case Nil{}:
      []
    case Con{+o, rest}:
      List.append(
        &2,
        Output,
        Bool.pick(List<&2, Output>, Output.persists(o), [], [o]),
        Outputs.messages(rest)
      )

# the outputs os persist the record r
def PersistsRecord(os: List<&2, Output>, r: SignedRecords.SignedRecord) -> Type:
  match os:
    case Nil{}:
      Empty
    case Con{PersistRecord{x}, rest}:
      {x == r: SignedRecords.SignedRecord} | PersistsRecord(rest, r)
    case Con{o, rest}:
      PersistsRecord(rest, r)

# the outputs os persist the part ws
def PersistsWords(os: List<&2, Output>, ws: List<&2, U32>) -> Type:
  match os:
    case Nil{}:
      Empty
    case Con{PersistPart{x}, rest}:
      {x == ws: List<&2, U32>} | PersistsWords(rest, ws)
    case Con{o, rest}:
      PersistsWords(rest, ws)

# the outputs os of the node st after the deed d, other than those that persist,
# are what d asks: a reply to a question; the opening of a sync; the reply to a
# sync message, when it is not empty; the answer to a part ask; on a Work, one
# fetch of exactly the needed parts that the node lacks; nothing otherwise
def ExpectedMessages(
  ~needed: SignedRecords.SignedRecordSet() -> List<&2, Shared.FixedLengthList(U32, 8n)>,
  ~answer: SignedRecords.SignedRecordSet() -> PartStore.PartStore -> List<&2, U32> -> List<&2, U32>,
  st: NodeState,
  d: Deed,
  os: List<&2, Output>
) -> Type:
  match d:
    case ClientAsks{c, q}:
      {
        Outputs.messages(
          os
        )
          == [
            ReplyToClient{c, answer(NodeState.records(st), NodeState.parts(st), q)}
          ]: List<&2, Output>
      }
    case PeerOpensSync{p}:
      {
        Outputs.messages(
          os
        )
          == [SendSync{p, RecordSync.RecordSync.opening(NodeState.records(st))}]: List<&2, Output>
      }
    case PeerSyncMessage{p, m}:
      (
        {
          RecordSync.RecordSync.reply(NodeState.records(st), m) == []: List<&2, U32>
        }
          & {Outputs.messages(os) == []: List<&2, Output>}
      )
        | (
          (
            {RecordSync.RecordSync.reply(NodeState.records(st), m) == []: List<&2, U32>} -> Empty
          )
            & {
              Outputs.messages(
                os
              )
                == [
                  SendSync{p, RecordSync.RecordSync.reply(NodeState.records(st), m)}
                ]: List<&2, Output>
            }
        )
    case PeerAsksParts{p, m}:
      {
        Outputs.messages(
          os
        )
          == [SendParts{p, PartStore.PartFetch.answer(NodeState.parts(st), m)}]: List<&2, Output>
      }
    case NodeWorks{}:
      Exists(
        List<&2, Shared.FixedLengthList(U32, 8n)>,
        hs => {
          Outputs.messages(os) == [FetchParts{hs}]: List<&2, Output>
        }
          & (
            @h: Shared.FixedLengthList(
              U32,
              8n
            ) -> (
              {
                PartStore.has_hash(hs, h) == True{}: Bool
              } -> {
                PartStore.has_hash(needed(NodeState.records(st)), h) == True{}: Bool
              }
                & {
                  Maybe.is_none(
                    &2,
                    List<&2, U32>,
                    PartStore.PartStore.get(NodeState.parts(st), h)
                  )
                    == True{}: Bool
                }
            )
              & (
                {
                  PartStore.has_hash(needed(NodeState.records(st)), h) == True{}: Bool
                } -> {
                  Maybe.is_none(
                    &2,
                    List<&2, U32>,
                    PartStore.PartStore.get(NodeState.parts(st), h)
                  )
                    == True{}: Bool
                } -> {PartStore.has_hash(hs, h) == True{}: Bool}
              )
          )
      )
    case _:
      {Outputs.messages(os) == []: List<&2, Output>}

# the plan ps has the step s with the payload p
def Plan.has(
  ps: List<&2, +Sigma<SlotConsensus.Step, _ => List<&2, U32>>>,
  +s: SlotConsensus.Step,
  +p: List<&2, U32>
) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case Con{(t, q), rest}:
      Bool.or(
        Bool.and(SlotConsensus.Step.same(t, s), WordListSets.same(q, p)),
        Plan.has(rest, s, p)
      )
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the voter me, among the voters vs of the step s, casts c next from the records
# rs, with the payload p, ticked or not
def Casts(
  ~decode: List<&2, U32> -> OwnerGroups.DecodedChoice,
  ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>,
  ~encode_choice: Nat -> List<&2, U32> -> List<&2, U32>,
  config: NodeConfig,
  rs: SignedRecords.SignedRecordSet(),
  me: List<&2, U32>,
  s: SlotConsensus.Step,
  p: List<&2, U32>,
  ticked: Bool,
  c: SlotConsensus.BallotToSign
) -> Type:
  match config:
    case NodeConfig{root, genesis, ks, n}:
      Exists(
        List<&2, List<&2, U32>>,
        vs => {
          OwnerGroups.voters(
            ~decode,
            s,
            root,
            genesis,
            RecordViews.RecordViews.ballots(~ballot_of, rs)
          )
            == MonotoneQueries.Known{vs}: MonotoneQueries.MonotoneAnswer<List<&2, List<&2, U32>>>
        }
          & {
            SlotConsensus.SlotConsensus.next_ballot(
              ~OwnerGroups.RootContext,
              ~(ctx => step => all => x => OwnerGroups.acceptable(~decode, ctx, step, all, x)),
              OwnerGroups.RootContext{root, genesis},
              vs,
              s,
              RecordViews.RecordViews.ballots(~ballot_of, rs),
              me,
              encode_choice(
                OwnerGroups.known_eras(
                  ~decode,
                  root,
                  genesis,
                  RecordViews.RecordViews.ballots(~ballot_of, rs)
                ),
                p
              ),
              ticked
            )
              == Some{c}: Maybe<&2, SlotConsensus.BallotToSign>
          }
      )

# Laws
# ----

# Means: a new node holds what every node holds (the invariant), has no client,
# has not stopped, and holds no record and no part.
# For free: every node that the program starts begins sound.
# For the goal: a node starts on its data address with nothing but its key.
# Example: a new node of key K is named K, holds nothing, and runs.
law Node.start_is_sound:
  for ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>
  for ~ballot_body: RecordViews.BallotBody -> List<&2, U32>
  for ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>
  for ~claim_body: Shared.FixedLengthList(U32, 8n) -> List<&2, U32>
  for ~decode: List<&2, U32> -> OwnerGroups.DecodedChoice
  for ~encode_choice: Nat -> List<&2, U32> -> List<&2, U32>
  for ~plan: SignedRecords.SignedRecordSet() -> List<
    &2,
    +Sigma<SlotConsensus.Step, _ => List<&2, U32>>>
  for ~needed: SignedRecords.SignedRecordSet() -> List<&2, Shared.FixedLengthList(U32, 8n)>
  for ~answer: SignedRecords.SignedRecordSet() -> PartStore.PartStore -> List<
    &2,
    U32> -> List<&2, U32>
  for config: NodeConfig
  for signer: Signatures.Signer
  for k: List<&2, U32>
  for h: Shared.FixedLengthList(U32, 8n)
  Invariant(
    ~ballot_of,
    Node.start(
      ~ballot_of,
      ~ballot_body,
      ~claim_of,
      ~claim_body,
      ~decode,
      ~encode_choice,
      ~plan,
      ~needed,
      ~answer,
      config,
      signer
    )
  )
    & (
      {
        NodeState.clients(
          Node.start(
            ~ballot_of,
            ~ballot_body,
            ~claim_of,
            ~claim_body,
            ~decode,
            ~encode_choice,
            ~plan,
            ~needed,
            ~answer,
            config,
            signer
          )
        )
          == []: List<&2, List<&2, U32>>
      }
        & (
          {
            NodeState.stopped(
              Node.start(
                ~ballot_of,
                ~ballot_body,
                ~claim_of,
                ~claim_body,
                ~decode,
                ~encode_choice,
                ~plan,
                ~needed,
                ~answer,
                config,
                signer
              )
            )
              == False{}: Bool
          }
            & (
              (
                SignedRecords.Has(
                  NodeState.records(
                    Node.start(
                      ~ballot_of,
                      ~ballot_body,
                      ~claim_of,
                      ~claim_body,
                      ~decode,
                      ~encode_choice,
                      ~plan,
                      ~needed,
                      ~answer,
                      config,
                      signer
                    )
                  ),
                  k
                ) -> Empty
              )
                & {
                  PartStore.PartStore.get(
                    NodeState.parts(
                      Node.start(
                        ~ballot_of,
                        ~ballot_body,
                        ~claim_of,
                        ~claim_body,
                        ~decode,
                        ~encode_choice,
                        ~plan,
                        ~needed,
                        ~answer,
                        config,
                        signer
                      )
                    ),
                    h
                  )
                    == None{}: Maybe<&2, List<&2, U32>>
                }
            )
        )
    )

# Means: a resumed node holds what every node holds, and holds exactly the
# persisted records (by key) and every persisted part.
# For free: a node resumes on its data address after a crash, sound; a log in
# which a record does not check, or the node's own ballots contradict, is
# refused, so a node never resumes into a lie.
# For the goal: a node starts or resumes on a data address (Node); together
# with the write-ahead law, a node that restarts never signs against its own
# earlier ballots (Trust 3).
# Example: a node that persisted 40 records resumes holding those 40.
law Node.resume_is_sound:
  for ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>
  for ~ballot_body: RecordViews.BallotBody -> List<&2, U32>
  for ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>
  for ~claim_body: Shared.FixedLengthList(U32, 8n) -> List<&2, U32>
  for ~decode: List<&2, U32> -> OwnerGroups.DecodedChoice
  for ~encode_choice: Nat -> List<&2, U32> -> List<&2, U32>
  for ~plan: SignedRecords.SignedRecordSet() -> List<
    &2,
    +Sigma<SlotConsensus.Step, _ => List<&2, U32>>>
  for ~needed: SignedRecords.SignedRecordSet() -> List<&2, Shared.FixedLengthList(U32, 8n)>
  for ~answer: SignedRecords.SignedRecordSet() -> PartStore.PartStore -> List<
    &2,
    U32> -> List<&2, U32>
  for config: NodeConfig
  for signer: Signatures.Signer
  for records: List<&2, SignedRecords.SignedRecord>
  for contents: List<&2, List<&2, U32>>
  for st: NodeState
  for k: List<&2, U32>
  for ws: List<&2, U32>
  {
    Node.resume(
      ~ballot_of,
      ~ballot_body,
      ~claim_of,
      ~claim_body,
      ~decode,
      ~encode_choice,
      ~plan,
      ~needed,
      ~answer,
      config,
      signer,
      records,
      contents
    )
      == Some{st}: Maybe<&1, NodeState>
  }
    -> Invariant(
      ~ballot_of,
      st
    )
      & (
        {
          NodeState.clients(st) == []: List<&2, List<&2, U32>>
        }
          & {NodeState.stopped(st) == False{}: Bool}
      )
      & (
        (
          SignedRecords.Has(NodeState.records(st), k) -> KeyIn(records, k)
        )
          & (
            {
              WordListSets.contains(contents, ws) == True{}: Bool
            } -> {
              PartStore.PartStore.get(
                NodeState.parts(st),
                Sha256.Sha256.of_words(ws)
              )
                == Some{ws}: Maybe<&2, List<&2, U32>>
            }
          )
      )

# Means: every step keeps what every node holds.
# For free: with the two laws above, every node that the program ever runs
# holds only records that check, never contradicts its own ballots, and is
# named by its key.
# For the goal: nothing that a client or a peer sends is kept unless it checks,
# and the program's own voters never lie (Trust 3).
# Example: a node that takes in a forged record still holds only records that
# check.
law Node.step_keeps_invariant:
  for ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>
  for ~ballot_body: RecordViews.BallotBody -> List<&2, U32>
  for ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>
  for ~claim_body: Shared.FixedLengthList(U32, 8n) -> List<&2, U32>
  for ~decode: List<&2, U32> -> OwnerGroups.DecodedChoice
  for ~encode_choice: Nat -> List<&2, U32> -> List<&2, U32>
  for ~plan: SignedRecords.SignedRecordSet() -> List<
    &2,
    +Sigma<SlotConsensus.Step, _ => List<&2, U32>>>
  for ~needed: SignedRecords.SignedRecordSet() -> List<&2, Shared.FixedLengthList(U32, 8n)>
  for ~answer: SignedRecords.SignedRecordSet() -> PartStore.PartStore -> List<
    &2,
    U32> -> List<&2, U32>
  for config: NodeConfig
  for st: NodeState
  for d: Deed
  BallotCodec(~ballot_of, ~ballot_body)
    -> ClaimCodec(~claim_of, ~claim_body)
    -> Invariant(~ballot_of, st)
    -> Invariant(
      ~ballot_of,
      Pair.fst(
        NodeState,
        List<&2, Output>,
        Node.step(
          ~ballot_of,
          ~ballot_body,
          ~claim_of,
          ~claim_body,
          ~decode,
          ~encode_choice,
          ~plan,
          ~needed,
          ~answer,
          config,
          st,
          d
        )
      )
    )

# Means: no step loses a record.
# For free: records only accumulate (the history is kept, as the plan says);
# answers of monotone queries only move forward on a node.
# For the goal: a node never loses a change that it holds (Behavior 1).
# Example: a node that holds a write still holds it after any deed.
law Node.step_keeps_records:
  for ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>
  for ~ballot_body: RecordViews.BallotBody -> List<&2, U32>
  for ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>
  for ~claim_body: Shared.FixedLengthList(U32, 8n) -> List<&2, U32>
  for ~decode: List<&2, U32> -> OwnerGroups.DecodedChoice
  for ~encode_choice: Nat -> List<&2, U32> -> List<&2, U32>
  for ~plan: SignedRecords.SignedRecordSet() -> List<
    &2,
    +Sigma<SlotConsensus.Step, _ => List<&2, U32>>>
  for ~needed: SignedRecords.SignedRecordSet() -> List<&2, Shared.FixedLengthList(U32, 8n)>
  for ~answer: SignedRecords.SignedRecordSet() -> PartStore.PartStore -> List<
    &2,
    U32> -> List<&2, U32>
  for config: NodeConfig
  for st: NodeState
  for d: Deed
  for k: List<&2, U32>
  SignedRecords.Has(
    NodeState.records(st),
    k
  ) -> SignedRecords.Has(
    NodeState.records(
      Pair.fst(
        NodeState,
        List<&2, Output>,
        Node.step(
          ~ballot_of,
          ~ballot_body,
          ~claim_of,
          ~claim_body,
          ~decode,
          ~encode_choice,
          ~plan,
          ~needed,
          ~answer,
          config,
          st,
          d
        )
      )
    ),
    k
  )

# Means: a step persists exactly the records and parts that it adds, and every
# output that persists comes before every output that does not.
# For free: storage holds every record before any message mentions it; a node
# that crashes after a step resumes with all that it signed.
# For the goal: a node resumes without losing its own ballots, so it never
# signs against them (Trust 3); "starts or resumes on a data address" (Node).
# Example: a Work that casts a vote outputs Persist of that vote before any
# Fetch.
law Node.step_persists_first:
  for ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>
  for ~ballot_body: RecordViews.BallotBody -> List<&2, U32>
  for ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>
  for ~claim_body: Shared.FixedLengthList(U32, 8n) -> List<&2, U32>
  for ~decode: List<&2, U32> -> OwnerGroups.DecodedChoice
  for ~encode_choice: Nat -> List<&2, U32> -> List<&2, U32>
  for ~plan: SignedRecords.SignedRecordSet() -> List<
    &2,
    +Sigma<SlotConsensus.Step, _ => List<&2, U32>>>
  for ~needed: SignedRecords.SignedRecordSet() -> List<&2, Shared.FixedLengthList(U32, 8n)>
  for ~answer: SignedRecords.SignedRecordSet() -> PartStore.PartStore -> List<
    &2,
    U32> -> List<&2, U32>
  for config: NodeConfig
  for st: NodeState
  for d: Deed
  for k: List<&2, U32>
  for h: Shared.FixedLengthList(U32, 8n)
  {
    Outputs.persist_first(
      Pair.snd(
        NodeState,
        List<&2, Output>,
        Node.step(
          ~ballot_of,
          ~ballot_body,
          ~claim_of,
          ~claim_body,
          ~decode,
          ~encode_choice,
          ~plan,
          ~needed,
          ~answer,
          config,
          st,
          d
        )
      )
    )
      == True{}: Bool
  }
    & (
      (
        SignedRecords.Has(
          NodeState.records(
            Pair.fst(
              NodeState,
              List<&2, Output>,
              Node.step(
                ~ballot_of,
                ~ballot_body,
                ~claim_of,
                ~claim_body,
                ~decode,
                ~encode_choice,
                ~plan,
                ~needed,
                ~answer,
                config,
                st,
                d
              )
            )
          ),
          k
        ) -> (
          SignedRecords.Has(
            NodeState.records(st),
            k
          )
            | PersistsKey(
              Pair.snd(
                NodeState,
                List<&2, Output>,
                Node.step(
                  ~ballot_of,
                  ~ballot_body,
                  ~claim_of,
                  ~claim_body,
                  ~decode,
                  ~encode_choice,
                  ~plan,
                  ~needed,
                  ~answer,
                  config,
                  st,
                  d
                )
              ),
              k
            )
        )
      )
        & (
          {
            Maybe.is_some(
              &2,
              List<&2, U32>,
              PartStore.PartStore.get(
                NodeState.parts(
                  Pair.fst(
                    NodeState,
                    List<&2, Output>,
                    Node.step(
                      ~ballot_of,
                      ~ballot_body,
                      ~claim_of,
                      ~claim_body,
                      ~decode,
                      ~encode_choice,
                      ~plan,
                      ~needed,
                      ~answer,
                      config,
                      st,
                      d
                    )
                  )
                ),
                h
              )
            )
              == True{}: Bool
          } -> (
            {
              Maybe.is_some(
                &2,
                List<&2, U32>,
                PartStore.PartStore.get(NodeState.parts(st), h)
              )
                == True{}: Bool
            }
              | PersistsPart(
                Pair.snd(
                  NodeState,
                  List<&2, Output>,
                  Node.step(
                    ~ballot_of,
                    ~ballot_body,
                    ~claim_of,
                    ~claim_body,
                    ~decode,
                    ~encode_choice,
                    ~plan,
                    ~needed,
                    ~answer,
                    config,
                    st,
                    d
                  )
                ),
                h
              )
          )
        )
        & (
          @r: SignedRecords.SignedRecord -> PersistsRecord(
            Pair.snd(
              NodeState,
              List<&2, Output>,
              Node.step(
                ~ballot_of,
                ~ballot_body,
                ~claim_of,
                ~claim_body,
                ~decode,
                ~encode_choice,
                ~plan,
                ~needed,
                ~answer,
                config,
                st,
                d
              )
            ),
            r
          ) -> SignedRecords.Has(
            NodeState.records(
              Pair.fst(
                NodeState,
                List<&2, Output>,
                Node.step(
                  ~ballot_of,
                  ~ballot_body,
                  ~claim_of,
                  ~claim_body,
                  ~decode,
                  ~encode_choice,
                  ~plan,
                  ~needed,
                  ~answer,
                  config,
                  st,
                  d
                )
              )
            ),
            SignedRecords.SignedRecord.key(r)
          )
            & (SignedRecords.Has(NodeState.records(st), SignedRecords.SignedRecord.key(r)) -> Empty)
        )
        & (
          @ws: List<
            &2,
            U32> -> PersistsWords(
            Pair.snd(
              NodeState,
              List<&2, Output>,
              Node.step(
                ~ballot_of,
                ~ballot_body,
                ~claim_of,
                ~claim_body,
                ~decode,
                ~encode_choice,
                ~plan,
                ~needed,
                ~answer,
                config,
                st,
                d
              )
            ),
            ws
          ) -> {
            PartStore.PartStore.get(
              NodeState.parts(
                Pair.fst(
                  NodeState,
                  List<&2, Output>,
                  Node.step(
                    ~ballot_of,
                    ~ballot_body,
                    ~claim_of,
                    ~claim_body,
                    ~decode,
                    ~encode_choice,
                    ~plan,
                    ~needed,
                    ~answer,
                    config,
                    st,
                    d
                  )
                )
              ),
              Sha256.Sha256.of_words(ws)
            )
              == Some{ws}: Maybe<&2, List<&2, U32>>
          }
            & (
              {
                Maybe.is_some(
                  &2,
                  List<&2, U32>,
                  PartStore.PartStore.get(NodeState.parts(st), Sha256.Sha256.of_words(ws))
                )
                  == True{}: Bool
              } -> Empty
            )
        )
    )

# Means: the clients of a running node are exactly those that connected and
# did not leave; whether it stopped follows the stop rule; and a stopped node
# changes nothing and outputs nothing.
# For free: a node with a connected client or a mount refuses a stop that is
# not forced; a stopped node stays stopped.
# For the goal: unless forced, a node stops only when no resource is mounted
# and no writer is connected (Node).
# Example: a node with a connected writer is still running after StopAsked{False}.
law Node.clients_and_stop:
  for ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>
  for ~ballot_body: RecordViews.BallotBody -> List<&2, U32>
  for ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>
  for ~claim_body: Shared.FixedLengthList(U32, 8n) -> List<&2, U32>
  for ~decode: List<&2, U32> -> OwnerGroups.DecodedChoice
  for ~encode_choice: Nat -> List<&2, U32> -> List<&2, U32>
  for ~plan: SignedRecords.SignedRecordSet() -> List<
    &2,
    +Sigma<SlotConsensus.Step, _ => List<&2, U32>>>
  for ~needed: SignedRecords.SignedRecordSet() -> List<&2, Shared.FixedLengthList(U32, 8n)>
  for ~answer: SignedRecords.SignedRecordSet() -> PartStore.PartStore -> List<
    &2,
    U32> -> List<&2, U32>
  for config: NodeConfig
  for st: NodeState
  for d: Deed
  (
    {
      NodeState.stopped(st) == False{}: Bool
    } -> {
      WordListSets.same_set(
        NodeState.clients(
          Pair.fst(
            NodeState,
            List<&2, Output>,
            Node.step(
              ~ballot_of,
              ~ballot_body,
              ~claim_of,
              ~claim_body,
              ~decode,
              ~encode_choice,
              ~plan,
              ~needed,
              ~answer,
              config,
              st,
              d
            )
          )
        ),
        Deed.clients(d, NodeState.clients(st))
      )
        == True{}: Bool
    }
  )
    & (
      {
        NodeState.stopped(
          Pair.fst(
            NodeState,
            List<&2, Output>,
            Node.step(
              ~ballot_of,
              ~ballot_body,
              ~claim_of,
              ~claim_body,
              ~decode,
              ~encode_choice,
              ~plan,
              ~needed,
              ~answer,
              config,
              st,
              d
            )
          )
        )
          == Deed.stopped(d, NodeState.stopped(st), NodeState.clients(st)): Bool
      }
        & (
          {
            NodeState.stopped(st) == True{}: Bool
          } -> {
            NodeState.records(
              Pair.fst(
                NodeState,
                List<&2, Output>,
                Node.step(
                  ~ballot_of,
                  ~ballot_body,
                  ~claim_of,
                  ~claim_body,
                  ~decode,
                  ~encode_choice,
                  ~plan,
                  ~needed,
                  ~answer,
                  config,
                  st,
                  d
                )
              )
            )
              == NodeState.records(st): SignedRecords.SignedRecordSet()
          }
            & (
              {
                NodeState.parts(
                  Pair.fst(
                    NodeState,
                    List<&2, Output>,
                    Node.step(
                      ~ballot_of,
                      ~ballot_body,
                      ~claim_of,
                      ~claim_body,
                      ~decode,
                      ~encode_choice,
                      ~plan,
                      ~needed,
                      ~answer,
                      config,
                      st,
                      d
                    )
                  )
                )
                  == NodeState.parts(st): PartStore.PartStore
              }
                & {
                  Pair.snd(
                    NodeState,
                    List<&2, Output>,
                    Node.step(
                      ~ballot_of,
                      ~ballot_body,
                      ~claim_of,
                      ~claim_body,
                      ~decode,
                      ~encode_choice,
                      ~plan,
                      ~needed,
                      ~answer,
                      config,
                      st,
                      d
                    )
                  )
                    == []: List<&2, Output>
                }
            )
        )
    )

# Means: a deed that brings no record in (connect, leave, ask, sync opening,
# part ask, part answer, stop) leaves the records as they are, and a deed that
# brings no part in (all but submit, part answer and work) leaves the parts as
# they are; and every step outputs, besides what it persists, exactly what its
# deed asks.
# For free: questions never change a node; a node sends nothing that its deed
# did not ask for, so its peers and clients see only replies and messages that
# the laws say.
# For the goal: what a node answers depends only on its records and parts
# (Behavior 1), and the program is this step and nothing else (no other output).
# Example: an Ask leaves the records and parts as they were and outputs only
# the reply.
law Node.step_does_what_its_deed_asks:
  for ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>
  for ~ballot_body: RecordViews.BallotBody -> List<&2, U32>
  for ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>
  for ~claim_body: Shared.FixedLengthList(U32, 8n) -> List<&2, U32>
  for ~decode: List<&2, U32> -> OwnerGroups.DecodedChoice
  for ~encode_choice: Nat -> List<&2, U32> -> List<&2, U32>
  for ~plan: SignedRecords.SignedRecordSet() -> List<
    &2,
    +Sigma<SlotConsensus.Step, _ => List<&2, U32>>>
  for ~needed: SignedRecords.SignedRecordSet() -> List<&2, Shared.FixedLengthList(U32, 8n)>
  for ~answer: SignedRecords.SignedRecordSet() -> PartStore.PartStore -> List<
    &2,
    U32> -> List<&2, U32>
  for config: NodeConfig
  for st: NodeState
  for d: Deed
  (
    {
      Deed.keeps_records(d) == True{}: Bool
    } -> {
      NodeState.records(
        Pair.fst(
          NodeState,
          List<&2, Output>,
          Node.step(
            ~ballot_of,
            ~ballot_body,
            ~claim_of,
            ~claim_body,
            ~decode,
            ~encode_choice,
            ~plan,
            ~needed,
            ~answer,
            config,
            st,
            d
          )
        )
      )
        == NodeState.records(st): SignedRecords.SignedRecordSet()
    }
  )
    & (
      (
        {
          Deed.keeps_parts(d) == True{}: Bool
        } -> {
          NodeState.parts(
            Pair.fst(
              NodeState,
              List<&2, Output>,
              Node.step(
                ~ballot_of,
                ~ballot_body,
                ~claim_of,
                ~claim_body,
                ~decode,
                ~encode_choice,
                ~plan,
                ~needed,
                ~answer,
                config,
                st,
                d
              )
            )
          )
            == NodeState.parts(st): PartStore.PartStore
        }
      )
        & (
          {
            NodeState.stopped(st) == False{}: Bool
          } -> ExpectedMessages(
            ~needed,
            ~answer,
            st,
            d,
            Pair.snd(
              NodeState,
              List<&2, Output>,
              Node.step(
                ~ballot_of,
                ~ballot_body,
                ~claim_of,
                ~claim_body,
                ~decode,
                ~encode_choice,
                ~plan,
                ~needed,
                ~answer,
                config,
                st,
                d
              )
            )
          )
        )
    )

# Means: a running node takes in a submitted record exactly when its client is
# connected, its signature checks, and its author is not the node; it then
# holds the record and every part that it carries, and nothing else new.
# For free: a writer's change reaches the node's records at once, before any
# decision (Writer: reads show their own changes); a forged record, or one
# signed in the node's own name, is refused.
# For the goal: a writer changes resources by request (Writer), and nothing it
# sends is kept unless it checks (Trust 3).
# Example: a connected writer submits a signed write with its content; the node
# holds the write and the content.
law Node.submit:
  for ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>
  for ~ballot_body: RecordViews.BallotBody -> List<&2, U32>
  for ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>
  for ~claim_body: Shared.FixedLengthList(U32, 8n) -> List<&2, U32>
  for ~decode: List<&2, U32> -> OwnerGroups.DecodedChoice
  for ~encode_choice: Nat -> List<&2, U32> -> List<&2, U32>
  for ~plan: SignedRecords.SignedRecordSet() -> List<
    &2,
    +Sigma<SlotConsensus.Step, _ => List<&2, U32>>>
  for ~needed: SignedRecords.SignedRecordSet() -> List<&2, Shared.FixedLengthList(U32, 8n)>
  for ~answer: SignedRecords.SignedRecordSet() -> PartStore.PartStore -> List<
    &2,
    U32> -> List<&2, U32>
  for config: NodeConfig
  for st: NodeState
  for c: List<&2, U32>
  for r: SignedRecords.SignedRecord
  for contents: List<&2, List<&2, U32>>
  for k: List<&2, U32>
  for ws: List<&2, U32>
  {NodeState.stopped(st) == False{}: Bool}
    -> (
      SignedRecords.Has(
        NodeState.records(
          Pair.fst(
            NodeState,
            List<&2, Output>,
            Node.step(
              ~ballot_of,
              ~ballot_body,
              ~claim_of,
              ~claim_body,
              ~decode,
              ~encode_choice,
              ~plan,
              ~needed,
              ~answer,
              config,
              st,
              ClientSubmits{c, r, contents}
            )
          )
        ),
        k
      ) -> (
        SignedRecords.Has(
          NodeState.records(st),
          k
        )
          | {SignedRecords.SignedRecord.key(r) == k: List<&2, U32>}
      )
    )
      & (
        {
          WordListSets.contains(NodeState.clients(st), c) == True{}: Bool
        } -> {
          SignedRecords.SignedRecord.signature_checks(r) == True{}: Bool
        } -> {
          WordListSets.same(author_of(r), NodeState.name(st)) == False{}: Bool
        } -> SignedRecords.Has(
          NodeState.records(
            Pair.fst(
              NodeState,
              List<&2, Output>,
              Node.step(
                ~ballot_of,
                ~ballot_body,
                ~claim_of,
                ~claim_body,
                ~decode,
                ~encode_choice,
                ~plan,
                ~needed,
                ~answer,
                config,
                st,
                ClientSubmits{c, r, contents}
              )
            )
          ),
          SignedRecords.SignedRecord.key(r)
        )
          & (
            {
              WordListSets.contains(contents, ws) == True{}: Bool
            } -> {
              Maybe.is_some(
                &2,
                List<&2, U32>,
                PartStore.PartStore.get(
                  NodeState.parts(
                    Pair.fst(
                      NodeState,
                      List<&2, Output>,
                      Node.step(
                        ~ballot_of,
                        ~ballot_body,
                        ~claim_of,
                        ~claim_body,
                        ~decode,
                        ~encode_choice,
                        ~plan,
                        ~needed,
                        ~answer,
                        config,
                        st,
                        ClientSubmits{c, r, contents}
                      )
                    )
                  ),
                  Sha256.Sha256.of_words(ws)
                )
              )
                == True{}: Bool
            }
          )
      )

# Means: a sync message from a peer makes the node hold exactly what record
# sync's take holds, except records in its own name that it did not hold.
# For free: record sync's laws hold on every node: syncs end and leave both
# nodes with the records of both; a peer cannot plant a record in the node's
# name.
# For the goal: a node that is behind catches up by itself, and checks
# everything it receives before it keeps it (Node, Behavior 1).
# Example: a peer's message with three new votes makes the node hold them and
# reply with what the peer lacks.
law Node.sync:
  for ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>
  for ~ballot_body: RecordViews.BallotBody -> List<&2, U32>
  for ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>
  for ~claim_body: Shared.FixedLengthList(U32, 8n) -> List<&2, U32>
  for ~decode: List<&2, U32> -> OwnerGroups.DecodedChoice
  for ~encode_choice: Nat -> List<&2, U32> -> List<&2, U32>
  for ~plan: SignedRecords.SignedRecordSet() -> List<
    &2,
    +Sigma<SlotConsensus.Step, _ => List<&2, U32>>>
  for ~needed: SignedRecords.SignedRecordSet() -> List<&2, Shared.FixedLengthList(U32, 8n)>
  for ~answer: SignedRecords.SignedRecordSet() -> PartStore.PartStore -> List<
    &2,
    U32> -> List<&2, U32>
  for config: NodeConfig
  for st: NodeState
  for p: List<&2, U32>
  for m: List<&2, U32>
  for k: List<&2, U32>
  {NodeState.stopped(st) == False{}: Bool}
    -> (
      (
        (
          SignedRecords.Has(
            NodeState.records(
              Pair.fst(
                NodeState,
                List<&2, Output>,
                Node.step(
                  ~ballot_of,
                  ~ballot_body,
                  ~claim_of,
                  ~claim_body,
                  ~decode,
                  ~encode_choice,
                  ~plan,
                  ~needed,
                  ~answer,
                  config,
                  st,
                  PeerSyncMessage{p, m}
                )
              )
            ),
            k
          ) -> SignedRecords.Has(
            RecordSync.RecordSync.take(NodeState.records(st), m),
            k
          )
            & (
              SignedRecords.Has(
                NodeState.records(st),
                k
              )
                | (
                  AuthoredBy(
                    NodeState.records(
                      Pair.fst(
                        NodeState,
                        List<&2, Output>,
                        Node.step(
                          ~ballot_of,
                          ~ballot_body,
                          ~claim_of,
                          ~claim_body,
                          ~decode,
                          ~encode_choice,
                          ~plan,
                          ~needed,
                          ~answer,
                          config,
                          st,
                          PeerSyncMessage{p, m}
                        )
                      )
                    ),
                    k,
                    NodeState.name(st)
                  ) -> Empty
                )
            )
        )
          & (
            SignedRecords.Has(
              RecordSync.RecordSync.take(NodeState.records(st), m),
              k
            ) -> (
              SignedRecords.Has(
                NodeState.records(st),
                k
              )
                | (
                  AuthoredBy(
                    RecordSync.RecordSync.take(NodeState.records(st), m),
                    k,
                    NodeState.name(st)
                  ) -> Empty
                )
            ) -> SignedRecords.Has(
              NodeState.records(
                Pair.fst(
                  NodeState,
                  List<&2, Output>,
                  Node.step(
                    ~ballot_of,
                    ~ballot_body,
                    ~claim_of,
                    ~claim_body,
                    ~decode,
                    ~encode_choice,
                    ~plan,
                    ~needed,
                    ~answer,
                    config,
                    st,
                    PeerSyncMessage{p, m}
                  )
                )
              ),
              k
            )
          )
      )
    )

# Means: a part answer is taken in as part fetch takes it.
# For free: part fetch's laws hold on every node: a fetch gives every asked
# part that the peer holds, and nothing wrong is kept.
# For the goal: each node keeps the part it uses and fetches the rest on demand
# (Store).
# Example: a peer asks for the part H, which the node holds; the node sends it.
law Node.parts:
  for ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>
  for ~ballot_body: RecordViews.BallotBody -> List<&2, U32>
  for ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>
  for ~claim_body: Shared.FixedLengthList(U32, 8n) -> List<&2, U32>
  for ~decode: List<&2, U32> -> OwnerGroups.DecodedChoice
  for ~encode_choice: Nat -> List<&2, U32> -> List<&2, U32>
  for ~plan: SignedRecords.SignedRecordSet() -> List<
    &2,
    +Sigma<SlotConsensus.Step, _ => List<&2, U32>>>
  for ~needed: SignedRecords.SignedRecordSet() -> List<&2, Shared.FixedLengthList(U32, 8n)>
  for ~answer: SignedRecords.SignedRecordSet() -> PartStore.PartStore -> List<
    &2,
    U32> -> List<&2, U32>
  for config: NodeConfig
  for st: NodeState
  for m: List<&2, U32>
  {NodeState.stopped(st) == False{}: Bool}
    -> {
      NodeState.parts(
        Pair.fst(
          NodeState,
          List<&2, Output>,
          Node.step(
            ~ballot_of,
            ~ballot_body,
            ~claim_of,
            ~claim_body,
            ~decode,
            ~encode_choice,
            ~plan,
            ~needed,
            ~answer,
            config,
            st,
            PeerAnswersParts{m}
          )
        )
      )
        == PartStore.PartFetch.take(NodeState.parts(st), m): PartStore.PartStore
    }

# Means: on a Work or a Tick, a running node signs, for each step that the plan
# names with its payload and whose voters are known, exactly the ballot that
# slot consensus says it casts next (with a proposal that names the latest
# known era), as long as its signer has room; it signs no other ballot.
# For free: every law of slot consensus about honest voters holds of the
# node's ballots: they never contradict its own, its leads and votes are judged
# sound and accepted, and good phases decide.
# For the goal: owner groups decide each step by a majority (Owner Group), and
# a slot gets decided once the network lets honest nodes hear one another
# (Trust 4, progress).
# Example: the plan names slot 5 of main; the node leads round 2 with its
# payload naming era 9, and signs that lead.
law Node.casts:
  for ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>
  for ~ballot_body: RecordViews.BallotBody -> List<&2, U32>
  for ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>
  for ~claim_body: Shared.FixedLengthList(U32, 8n) -> List<&2, U32>
  for ~decode: List<&2, U32> -> OwnerGroups.DecodedChoice
  for ~encode_choice: Nat -> List<&2, U32> -> List<&2, U32>
  for ~plan: SignedRecords.SignedRecordSet() -> List<
    &2,
    +Sigma<SlotConsensus.Step, _ => List<&2, U32>>>
  for ~needed: SignedRecords.SignedRecordSet() -> List<&2, Shared.FixedLengthList(U32, 8n)>
  for ~answer: SignedRecords.SignedRecordSet() -> PartStore.PartStore -> List<
    &2,
    U32> -> List<&2, U32>
  for config: NodeConfig
  for st: NodeState
  for ticked: Bool
  for k: List<&2, U32>
  for s: SlotConsensus.Step
  for i: Nat
  for r: Nat
  for a: SlotConsensus.BallotAction
  {NodeState.stopped(st) == False{}: Bool}
    -> BallotCodec(~ballot_of, ~ballot_body)
    -> (
      {
        List.contains(
          ~SlotConsensus.Ballot,
          ~SlotConsensus.Ballot.same,
          RecordViews.RecordViews.ballots(
            ~ballot_of,
            NodeState.records(
              Pair.fst(
                NodeState,
                List<&2, Output>,
                Node.step(
                  ~ballot_of,
                  ~ballot_body,
                  ~claim_of,
                  ~claim_body,
                  ~decode,
                  ~encode_choice,
                  ~plan,
                  ~needed,
                  ~answer,
                  config,
                  st,
                  Bool.pick(Deed, ticked, TimerTicks{}, NodeWorks{})
                )
              )
            )
          ),
          SlotConsensus.Ballot{k, NodeState.name(st), s, i, r, a}
        )
          == True{}: Bool
      } -> (
        {
          List.contains(
            ~SlotConsensus.Ballot,
            ~SlotConsensus.Ballot.same,
            RecordViews.RecordViews.ballots(~ballot_of, NodeState.records(st)),
            SlotConsensus.Ballot{k, NodeState.name(st), s, i, r, a}
          )
            == True{}: Bool
        }
          | Exists(
            List<&2, U32>,
            p => {
              Plan.has(plan(NodeState.records(st)), s, p) == True{}: Bool
            }
              & Casts(
                ~decode,
                ~ballot_of,
                ~encode_choice,
                config,
                NodeState.records(st),
                NodeState.name(st),
                s,
                p,
                ticked,
                SlotConsensus.BallotToSign{i, r, a}
              )
          )
      )
    )
      & (
        @p: List<
          &2,
          U32> -> {
          Plan.has(plan(NodeState.records(st)), s, p) == True{}: Bool
        } -> Casts(
          ~decode,
          ~ballot_of,
          ~encode_choice,
          config,
          NodeState.records(st),
          NodeState.name(st),
          s,
          p,
          ticked,
          SlotConsensus.BallotToSign{i, r, a}
        ) -> {
          Nat.is_lt(
            Nat.add(
              List.length(
                &2,
                +Sigma<SlotConsensus.Step, _ => List<&2, U32>>,
                plan(NodeState.records(st))
              ),
              List.length(&2, Shared.FixedLengthList(U32, 8n), needed(NodeState.records(st)))
            ),
            Pair.fst(Nat, Signatures.Signer, Signatures.Signer.remaining(NodeState.signer(st)))
          )
            == True{}: Bool
        } -> Exists(
          List<&2, U32>,
          k2 => {
            List.contains(
              ~SlotConsensus.Ballot,
              ~SlotConsensus.Ballot.same,
              RecordViews.RecordViews.ballots(
                ~ballot_of,
                NodeState.records(
                  Pair.fst(
                    NodeState,
                    List<&2, Output>,
                    Node.step(
                      ~ballot_of,
                      ~ballot_body,
                      ~claim_of,
                      ~claim_body,
                      ~decode,
                      ~encode_choice,
                      ~plan,
                      ~needed,
                      ~answer,
                      config,
                      st,
                      Bool.pick(Deed, ticked, TimerTicks{}, NodeWorks{})
                    )
                  )
                )
              ),
              SlotConsensus.Ballot{k2, NodeState.name(st), s, i, r, a}
            )
              == True{}: Bool
          }
        )
      )

# Means: on a Work, a running node that is a trusted keeper claims each needed
# part that it holds, and it drops parts exactly as part store's drop does with
# its claims, keepers, copies and needed parts.
# For free: part store's laws hold on every node: a part is dropped only once
# enough other keepers claimed it, and a keeper keeps what it claimed.
# For the goal: every part is kept by enough nodes to never be lost, and each
# node fetches the rest on demand (Store, Behavior 3).
# Example: a keeper that holds a needed part H signs a claim on H; a node that
# lacks a needed part H outputs Fetch of H.
law Node.work_parts:
  for ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>
  for ~ballot_body: RecordViews.BallotBody -> List<&2, U32>
  for ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>
  for ~claim_body: Shared.FixedLengthList(U32, 8n) -> List<&2, U32>
  for ~decode: List<&2, U32> -> OwnerGroups.DecodedChoice
  for ~encode_choice: Nat -> List<&2, U32> -> List<&2, U32>
  for ~plan: SignedRecords.SignedRecordSet() -> List<
    &2,
    +Sigma<SlotConsensus.Step, _ => List<&2, U32>>>
  for ~needed: SignedRecords.SignedRecordSet() -> List<&2, Shared.FixedLengthList(U32, 8n)>
  for ~answer: SignedRecords.SignedRecordSet() -> PartStore.PartStore -> List<
    &2,
    U32> -> List<&2, U32>
  for config: NodeConfig
  for st: NodeState
  for h: Shared.FixedLengthList(U32, 8n)
  {NodeState.stopped(st) == False{}: Bool}
    -> ClaimCodec(~claim_of, ~claim_body)
    -> (
      {
        NodeState.parts(
          Pair.fst(
            NodeState,
            List<&2, Output>,
            Node.step(
              ~ballot_of,
              ~ballot_body,
              ~claim_of,
              ~claim_body,
              ~decode,
              ~encode_choice,
              ~plan,
              ~needed,
              ~answer,
              config,
              st,
              NodeWorks{}
            )
          )
        )
          == PartStore.PartStore.drop(
            NodeState.parts(st),
            RecordViews.RecordViews.claims(~claim_of, NodeState.records(st)),
            NodeConfig.keepers(config),
            NodeConfig.copies(config),
            NodeState.name(st),
            needed(NodeState.records(st))
          ): PartStore.PartStore
      }
        & (
          (
            {
              PartStore.has_hash(needed(NodeState.records(st)), h) == True{}: Bool
            } -> {
              Maybe.is_some(
                &2,
                List<&2, U32>,
                PartStore.PartStore.get(NodeState.parts(st), h)
              )
                == True{}: Bool
            } -> {
              WordListSets.contains(NodeConfig.keepers(config), NodeState.name(st)) == True{}: Bool
            } -> {
              Nat.is_lt(
                Nat.add(
                  List.length(
                    &2,
                    +Sigma<SlotConsensus.Step, _ => List<&2, U32>>,
                    plan(NodeState.records(st))
                  ),
                  List.length(&2, Shared.FixedLengthList(U32, 8n), needed(NodeState.records(st)))
                ),
                Pair.fst(Nat, Signatures.Signer, Signatures.Signer.remaining(NodeState.signer(st)))
              )
                == True{}: Bool
            } -> RecordViews.IsClaim(
              ~claim_of,
              NodeState.records(
                Pair.fst(
                  NodeState,
                  List<&2, Output>,
                  Node.step(
                    ~ballot_of,
                    ~ballot_body,
                    ~claim_of,
                    ~claim_body,
                    ~decode,
                    ~encode_choice,
                    ~plan,
                    ~needed,
                    ~answer,
                    config,
                    st,
                    NodeWorks{}
                  )
                )
              ),
              NodeState.name(st),
              h
            )
          )
        )
    )

# Means: the records that a Work or a Tick adds in the node's own name are its
# ballots and its claims; it adds no record of anyone else.
# For free: with the two laws above, everything a node signs is a ballot that
# slot consensus allows or a claim on a needed part that it holds.
# For the goal: a node signs nothing that the laws above do not allow, so its
# signatures carry exactly the trust that Trust 3 asks of it.
# Example: a Work adds a vote and a claim, both in the node's name, and nothing
# else.
law Node.work_adds_only_own:
  for ~ballot_of: List<&2, U32> -> Maybe<&2, RecordViews.BallotBody>
  for ~ballot_body: RecordViews.BallotBody -> List<&2, U32>
  for ~claim_of: List<&2, U32> -> Maybe<&2, Shared.FixedLengthList(U32, 8n)>
  for ~claim_body: Shared.FixedLengthList(U32, 8n) -> List<&2, U32>
  for ~decode: List<&2, U32> -> OwnerGroups.DecodedChoice
  for ~encode_choice: Nat -> List<&2, U32> -> List<&2, U32>
  for ~plan: SignedRecords.SignedRecordSet() -> List<
    &2,
    +Sigma<SlotConsensus.Step, _ => List<&2, U32>>>
  for ~needed: SignedRecords.SignedRecordSet() -> List<&2, Shared.FixedLengthList(U32, 8n)>
  for ~answer: SignedRecords.SignedRecordSet() -> PartStore.PartStore -> List<
    &2,
    U32> -> List<&2, U32>
  for config: NodeConfig
  for st: NodeState
  for ticked: Bool
  for k: List<&2, U32>
  {NodeState.stopped(st) == False{}: Bool}
    -> SignedRecords.Has(
      NodeState.records(
        Pair.fst(
          NodeState,
          List<&2, Output>,
          Node.step(
            ~ballot_of,
            ~ballot_body,
            ~claim_of,
            ~claim_body,
            ~decode,
            ~encode_choice,
            ~plan,
            ~needed,
            ~answer,
            config,
            st,
            Bool.pick(Deed, ticked, TimerTicks{}, NodeWorks{})
          )
        )
      ),
      k
    )
    -> (
      SignedRecords.Has(
        NodeState.records(st),
        k
      )
        | AuthoredBy(
          NodeState.records(
            Pair.fst(
              NodeState,
              List<&2, Output>,
              Node.step(
                ~ballot_of,
                ~ballot_body,
                ~claim_of,
                ~claim_body,
                ~decode,
                ~encode_choice,
                ~plan,
                ~needed,
                ~answer,
                config,
                st,
                Bool.pick(Deed, ticked, TimerTicks{}, NodeWorks{})
              )
            )
          ),
          k,
          NodeState.name(st)
        )
    )
