import Base
import ../shared/shared/monotone_queries/spec.bend as MonotoneQueries
import ../shared/shared/shared/shared/word_list_sets/spec.bend as WordListSets
import ../shared/slot_consensus/spec.bend as SlotConsensus

# Owner groups say who the voters of each step are. One line, the root, holds
# the configuration: its decided choices set the members of groups and the
# owner group of lines. A member is a node or another group, and the nodes of
# a group are the names reached through it that are not groups.
#
# The voters of a step are the nodes of the owner group of its line, in the
# configuration of the step's era:
# - for the root, the configuration after all of the root's earlier slots;
# - for any other line, at first the configuration right after the root slot
#   that gave the line an owner, then, slot after slot, the era that the line's
#   previous decided choice names, never lower than the one before.
#
# A decided choice is read by a hook (decode): the changes it makes, and the
# era it names for the next slot. Every answer here is Unknown until the
# decisions it rests on are known, and Contradicted when one of them is.

# a change of the configuration: the members of a group, or the owner group of
# a line
type GroupChange is Data:
  SetMembers{group: List<&2, U32>, members: List<&2, List<&2, U32>>}
  SetOwner{line: List<&2, U32>, group: List<&2, U32>}

# a decided choice as owner groups read it: the changes it makes when it is a
# root slot's, and the era it names for the next slot when it is another
# line's
type DecodedChoice is Data:
  DecodedChoice{changes: List<&2, GroupChange>, next_era: Nat}

# a configuration: the members of each group and the owner group of each line,
# the latest first
type GroupConfig is Data:
  GroupConfig{
    members: List<&2, +Sigma<List<&2, U32>, _ => List<&2, List<&2, U32>>>>,
    owners: List<&2, +Sigma<List<&2, U32>, _ => List<&2, U32>>>
  }

# Configurations
# --------------

# cfg after the change c
def GroupConfig.apply(cfg: GroupConfig, c: GroupChange) -> GroupConfig:
  match cfg c:
    case GroupConfig{ms, os} SetMembers{g, xs}:
      GroupConfig{(g, xs) <> ms, os}
    case GroupConfig{ms, os} SetOwner{l, g}:
      GroupConfig{ms, (l, g) <> os}

# cfg after the changes cs, one after another
def GroupConfig.apply_all(cs: List<&2, GroupChange>, cfg: GroupConfig) -> GroupConfig:
  match cs:
    case Nil{}:
      cfg
    case Con{c, rest}:
      GroupConfig.apply_all(rest, GroupConfig.apply(cfg, c))

# found, or else the members that the latest entry of g in ms names, if g has
# one
def GroupConfig.lookup.go(
  ms: List<&2, +Sigma<List<&2, U32>, _ => List<&2, List<&2, U32>>>>,
  +g: List<&2, U32>,
  found: Maybe<&2, List<&2, List<&2, U32>>>
) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match ms:
    case Nil{}:
      found
    case Con{(h, xs), rest}:
      match found:
        case Some{x}:
          Some{x}
        case None{}:
          GroupConfig.lookup.go(
            rest,
            g,
            Bool.pick(Maybe<&2, List<&2, List<&2, U32>>>, WordListSets.same(h, g), Some{xs}, None{})
          )

# the members that the latest entry of g in ms names, if g has one
def GroupConfig.lookup(
  ms: List<&2, +Sigma<List<&2, U32>, _ => List<&2, List<&2, U32>>>>,
  g: List<&2, U32>
) -> Maybe<&2, List<&2, List<&2, U32>>>:
  GroupConfig.lookup.go(ms, g, None{})

# the members of the group g in cfg, if g is a group
def GroupConfig.members(cfg: GroupConfig, g: List<&2, U32>) -> Maybe<&2, List<&2, List<&2, U32>>>:
  match cfg:
    case GroupConfig{ms, os}:
      GroupConfig.lookup(ms, g)

# found, or else the group that the latest entry of the line l in os names, if
# any
def GroupConfig.owner.lookup.go(
  os: List<&2, +Sigma<List<&2, U32>, _ => List<&2, U32>>>,
  +l: List<&2, U32>,
  found: Maybe<&2, List<&2, U32>>
) -> Maybe<&2, List<&2, U32>>:
  match os:
    case Nil{}:
      found
    case Con{(m, g), rest}:
      match found:
        case Some{x}:
          Some{x}
        case None{}:
          GroupConfig.owner.lookup.go(
            rest,
            l,
            Bool.pick(Maybe<&2, List<&2, U32>>, WordListSets.same(m, l), Some{g}, None{})
          )

# the group that the latest entry of the line l in os names, if any
def GroupConfig.owner.lookup(
  os: List<&2, +Sigma<List<&2, U32>, _ => List<&2, U32>>>,
  l: List<&2, U32>
) -> Maybe<&2, List<&2, U32>>:
  GroupConfig.owner.lookup.go(os, l, None{})

# the owner group of the line l in cfg, if it has one
def GroupConfig.owner(cfg: GroupConfig, l: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match cfg:
    case GroupConfig{ms, os}:
      GroupConfig.owner.lookup(os, l)

# the names of xs that are not groups in ms
def GroupConfig.not_groups(
  xs: List<&2, List<&2, U32>>,
  +ms: List<&2, +Sigma<List<&2, U32>, _ => List<&2, List<&2, U32>>>>
) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      []
    case Con{+x, rest}:
      List.append(
        &2,
        List<&2, U32>,
        Bool.pick(
          List<&2, List<&2, U32>>,
          Maybe.is_none(&2, List<&2, List<&2, U32>>, GroupConfig.lookup(ms, x)),
          [x],
          []
        ),
        GroupConfig.not_groups(rest, ms)
      )

# the members m of the group x, unless x is in seen
def GroupConfig.expand.one(
  m: Maybe<&2, List<&2, List<&2, U32>>>,
  seen_x: Bool
) -> List<&2, List<&2, U32>>:
  match m seen_x:
    case Some{xs} False{}:
      xs
    case _ _:
      []

# the members of the groups of xs in ms that are not in seen
def GroupConfig.expand(
  xs: List<&2, List<&2, U32>>,
  +ms: List<&2, +Sigma<List<&2, U32>, _ => List<&2, List<&2, U32>>>>,
  +seen: List<&2, List<&2, U32>>
) -> List<&2, List<&2, U32>>:
  match xs:
    case Nil{}:
      []
    case Con{+x, rest}:
      List.append(
        &2,
        List<&2, U32>,
        GroupConfig.expand.one(GroupConfig.lookup(ms, x), WordListSets.contains(seen, x)),
        GroupConfig.expand(rest, ms, seen)
      )

# the names that are not groups, reached from the names frontier through the
# groups of ms in at most fuel steps, skipping the groups of seen
def GroupConfig.reach(
  fuel: Nat,
  +ms: List<&2, +Sigma<List<&2, U32>, _ => List<&2, List<&2, U32>>>>,
  +frontier: List<&2, List<&2, U32>>,
  +seen: List<&2, List<&2, U32>>
) -> List<&2, List<&2, U32>>:
  match fuel:
    case 0n:
      []
    case 1n+f:
      List.append(
        &2,
        List<&2, U32>,
        GroupConfig.not_groups(frontier, ms),
        GroupConfig.reach(
          f,
          ms,
          GroupConfig.expand(frontier, ms, seen),
          List.append(&2, List<&2, U32>, seen, frontier)
        )
      )

# the nodes of the name g in cfg, each once: the names reached through it that
# are not groups (g itself when it is not a group)
def GroupConfig.nodes(cfg: GroupConfig, g: List<&2, U32>) -> List<&2, List<&2, U32>>:
  match cfg:
    case GroupConfig{+ms, os}:
      WordListSets.dedupe(
        GroupConfig.reach(
          1n+List.length(&2, +Sigma<List<&2, U32>, _ => List<&2, List<&2, U32>>>, ms),
          ms,
          [g],
          []
        )
      )

# the voters of the line l in cfg: the nodes of its owner group, none if it
# has no owner
def GroupConfig.voters.of(m: Maybe<&2, List<&2, U32>>, cfg: GroupConfig) -> List<&2, List<&2, U32>>:
  match m:
    case None{}:
      []
    case Some{g}:
      GroupConfig.nodes(cfg, g)

# the voters of the line l in cfg
def GroupConfig.voters(+cfg: GroupConfig, l: List<&2, U32>) -> List<&2, List<&2, U32>>:
  GroupConfig.voters.of(GroupConfig.owner(cfg, l), cfg)

# Eras and voters
# ---------------

# cfg after the changes of the decoded choice d
def root_config.apply_decoded(d: DecodedChoice, cfg: GroupConfig) -> GroupConfig:
  match d:
    case DecodedChoice{cs, e}:
      GroupConfig.apply_all(cs, cfg)

# the answer for a decided choice a of a root slot, read by decode: the
# configuration cfg after its changes
def root_config.after_choice(
  ~decode: List<&2, U32> -> DecodedChoice,
  a: MonotoneQueries.MonotoneAnswer<List<&2, U32>>,
  cfg: GroupConfig
) -> MonotoneQueries.MonotoneAnswer<GroupConfig>:
  match a:
    case MonotoneQueries.Unknown{}:
      MonotoneQueries.Unknown{}
    case MonotoneQueries.Contradicted{p}:
      MonotoneQueries.Contradicted{p}
    case MonotoneQueries.Known{x}:
      MonotoneQueries.Known{root_config.apply_decoded(decode(x), cfg)}

# the configuration after root slot j, from the configuration c after the
# slots below j
def root_config.after(
  ~decode: List<&2, U32> -> DecodedChoice,
  c: MonotoneQueries.MonotoneAnswer<GroupConfig>,
  j: Nat,
  +root: List<&2, U32>,
  all: List<&2, SlotConsensus.Ballot>
) -> MonotoneQueries.MonotoneAnswer<GroupConfig>:
  match c:
    case MonotoneQueries.Unknown{}:
      MonotoneQueries.Unknown{}
    case MonotoneQueries.Contradicted{p}:
      MonotoneQueries.Contradicted{p}
    case MonotoneQueries.Known{+cfg}:
      root_config.after_choice(
        ~decode,
        SlotConsensus.SlotConsensus.decision(
          GroupConfig.voters(cfg, root),
          SlotConsensus.Step{root, j},
          all
        ),
        cfg
      )

# the root configuration after the root slots below k, with the ballots all
# and the changes genesis that start the root
def root_config(
  ~decode: List<&2, U32> -> DecodedChoice,
  +k: Nat,
  +root: List<&2, U32>,
  genesis: List<&2, GroupChange>,
  +all: List<&2, SlotConsensus.Ballot>
) -> MonotoneQueries.MonotoneAnswer<GroupConfig>:
  match k:
    case 0n:
      MonotoneQueries.Known{GroupConfig.apply_all(genesis, GroupConfig{[], []})}
    case 1n+j:
      root_config.after(~decode, root_config(~decode, j, root, genesis, all), j, root, all)

# era k when the configuration c gives the line l an owner, else later
def creation_era.at(
  c: MonotoneQueries.MonotoneAnswer<GroupConfig>,
  k: Nat,
  l: List<&2, U32>,
  later: MonotoneQueries.MonotoneAnswer<Nat>
) -> MonotoneQueries.MonotoneAnswer<Nat>:
  match c:
    case MonotoneQueries.Unknown{}:
      MonotoneQueries.Unknown{}
    case MonotoneQueries.Contradicted{p}:
      MonotoneQueries.Contradicted{p}
    case MonotoneQueries.Known{cfg}:
      Bool.pick(
        MonotoneQueries.MonotoneAnswer<Nat>,
        Maybe.is_some(&2, List<&2, U32>, GroupConfig.owner(cfg, l)),
        MonotoneQueries.Known{k},
        later
      )

# the era of the first configuration, from k on and within fuel more, in which
# the line l has an owner: Unknown while none is known yet
def creation_era.search(
  ~decode: List<&2, U32> -> DecodedChoice,
  fuel: Nat,
  +k: Nat,
  +l: List<&2, U32>,
  +root: List<&2, U32>,
  +genesis: List<&2, GroupChange>,
  +all: List<&2, SlotConsensus.Ballot>
) -> MonotoneQueries.MonotoneAnswer<Nat>:
  match fuel:
    case 0n:
      MonotoneQueries.Unknown{}
    case 1n+f:
      creation_era.at(
        root_config(~decode, k, root, genesis, all),
        k,
        l,
        creation_era.search(~decode, f, 1n+k, l, root, genesis, all)
      )

# the era of the first configuration in which the line l has an owner; the
# root slots that the ballots all can decide are at most as many as the
# ballots
def creation_era(
  ~decode: List<&2, U32> -> DecodedChoice,
  l: List<&2, U32>,
  root: List<&2, U32>,
  genesis: List<&2, GroupChange>,
  +all: List<&2, SlotConsensus.Ballot>
) -> MonotoneQueries.MonotoneAnswer<Nat>:
  creation_era.search(
    ~decode,
    1n+List.length(&2, SlotConsensus.Ballot, all),
    0n,
    l,
    root,
    genesis,
    all
  )

# the era that the decoded choice d names, never lower than m
def era.of_decoded(d: DecodedChoice, m: Nat) -> Nat:
  match d:
    case DecodedChoice{cs, e}:
      Nat.max(m, e)

# the era after a decided choice a of the line, read by decode, from the era m
# of its slot: the era it names, never lower than m
def era.after_choice(
  ~decode: List<&2, U32> -> DecodedChoice,
  a: MonotoneQueries.MonotoneAnswer<List<&2, U32>>,
  m: Nat
) -> MonotoneQueries.MonotoneAnswer<Nat>:
  match a:
    case MonotoneQueries.Unknown{}:
      MonotoneQueries.Unknown{}
    case MonotoneQueries.Contradicted{p}:
      MonotoneQueries.Contradicted{p}
    case MonotoneQueries.Known{x}:
      MonotoneQueries.Known{era.of_decoded(decode(x), m)}

# the era of slot j of the line l after the configuration c of its era m
def era.after_config(
  ~decode: List<&2, U32> -> DecodedChoice,
  c: MonotoneQueries.MonotoneAnswer<GroupConfig>,
  m: Nat,
  j: Nat,
  +l: List<&2, U32>,
  all: List<&2, SlotConsensus.Ballot>
) -> MonotoneQueries.MonotoneAnswer<Nat>:
  match c:
    case MonotoneQueries.Unknown{}:
      MonotoneQueries.Unknown{}
    case MonotoneQueries.Contradicted{p}:
      MonotoneQueries.Contradicted{p}
    case MonotoneQueries.Known{cfg}:
      era.after_choice(
        ~decode,
        SlotConsensus.SlotConsensus.decision(
          GroupConfig.voters(cfg, l),
          SlotConsensus.Step{l, j},
          all
        ),
        m
      )

# the era of slot j+1 of the line l, from the era e of slot j
def era.next(
  ~decode: List<&2, U32> -> DecodedChoice,
  e: MonotoneQueries.MonotoneAnswer<Nat>,
  j: Nat,
  l: List<&2, U32>,
  root: List<&2, U32>,
  genesis: List<&2, GroupChange>,
  +all: List<&2, SlotConsensus.Ballot>
) -> MonotoneQueries.MonotoneAnswer<Nat>:
  match e:
    case MonotoneQueries.Unknown{}:
      MonotoneQueries.Unknown{}
    case MonotoneQueries.Contradicted{p}:
      MonotoneQueries.Contradicted{p}
    case MonotoneQueries.Known{+m}:
      era.after_config(~decode, root_config(~decode, m, root, genesis, all), m, j, l, all)

# the era of slot k of the line l, which is not the root
def era(
  ~decode: List<&2, U32> -> DecodedChoice,
  +k: Nat,
  +l: List<&2, U32>,
  +root: List<&2, U32>,
  +genesis: List<&2, GroupChange>,
  +all: List<&2, SlotConsensus.Ballot>
) -> MonotoneQueries.MonotoneAnswer<Nat>:
  match k:
    case 0n:
      creation_era(~decode, l, root, genesis, all)
    case 1n+j:
      era.next(~decode, era(~decode, j, l, root, genesis, all), j, l, root, genesis, all)

# the voters of the line l in the configuration c
def voters.in(
  c: MonotoneQueries.MonotoneAnswer<GroupConfig>,
  l: List<&2, U32>
) -> MonotoneQueries.MonotoneAnswer<List<&2, List<&2, U32>>>:
  match c:
    case MonotoneQueries.Unknown{}:
      MonotoneQueries.Unknown{}
    case MonotoneQueries.Contradicted{p}:
      MonotoneQueries.Contradicted{p}
    case MonotoneQueries.Known{cfg}:
      MonotoneQueries.Known{GroupConfig.voters(cfg, l)}

# the voters of the line l in the configuration of the era e
def voters.at_era(
  ~decode: List<&2, U32> -> DecodedChoice,
  e: MonotoneQueries.MonotoneAnswer<Nat>,
  l: List<&2, U32>,
  root: List<&2, U32>,
  genesis: List<&2, GroupChange>,
  all: List<&2, SlotConsensus.Ballot>
) -> MonotoneQueries.MonotoneAnswer<List<&2, List<&2, U32>>>:
  match e:
    case MonotoneQueries.Unknown{}:
      MonotoneQueries.Unknown{}
    case MonotoneQueries.Contradicted{p}:
      MonotoneQueries.Contradicted{p}
    case MonotoneQueries.Known{m}:
      voters.in(root_config(~decode, m, root, genesis, all), l)

# the voters of slot k of the line l: of the root when is_root, else of another
# line
def voters.by_line(
  ~decode: List<&2, U32> -> DecodedChoice,
  is_root: Bool,
  +l: List<&2, U32>,
  k: Nat,
  +root: List<&2, U32>,
  +genesis: List<&2, GroupChange>,
  +all: List<&2, SlotConsensus.Ballot>
) -> MonotoneQueries.MonotoneAnswer<List<&2, List<&2, U32>>>:
  match is_root:
    case True{}:
      voters.in(root_config(~decode, k, root, genesis, all), root)
    case False{}:
      voters.at_era(~decode, era(~decode, k, l, root, genesis, all), l, root, genesis, all)

# the voters of the step: for a root slot k, the voters of the root after the
# root slots below k; for slot k of another line, the voters of that line in
# the configuration of the slot's era
def voters(
  ~decode: List<&2, U32> -> DecodedChoice,
  step: SlotConsensus.Step,
  +root: List<&2, U32>,
  genesis: List<&2, GroupChange>,
  all: List<&2, SlotConsensus.Ballot>
) -> MonotoneQueries.MonotoneAnswer<List<&2, List<&2, U32>>>:
  match step:
    case SlotConsensus.Step{+l, k}:
      voters.by_line(~decode, WordListSets.same(l, root), l, k, root, genesis, all)

# Laws
# ----

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- Reaches is a type: only laws use it, so no code that runs builds or frees xs
# the name v is reached from the name g in cfg through the names of path: each
# name before v is a group whose members hold the next one, and v is not a
# group
def Reaches(
  cfg: GroupConfig,
  g: List<&2, U32>,
  path: List<&2, List<&2, U32>>,
  v: List<&2, U32>
) -> Type:
  match path:
    case Nil{}:
      {
        GroupConfig.members(cfg, g) == None{}: Maybe<&2, List<&2, List<&2, U32>>>
      }
        & {g == v: List<&2, U32>}
    case Con{h, rest}:
      Exists(
        List<&2, List<&2, U32>>,
        xs => {
          GroupConfig.members(cfg, g) == Some{xs}: Maybe<&2, List<&2, List<&2, U32>>>
        }
          & ({WordListSets.contains(xs, h) == True{}: Bool} & Reaches(cfg, h, rest, v))
      )
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Means: the nodes of a name are exactly the names reached through it, by the
# members of groups, that are not groups themselves.
# For free: a group of groups has the nodes of all of them; a group that
# contains itself, or a cycle of groups, still has finitely many nodes; a node
# that no group reaches is never a voter.
# For the goal: groups can contain groups (Shape 4), and changing one group
# changes the voters of every line whose owner reaches it.
# Example: core holds the node a and the group ops; ops holds b and c; the
# nodes of core are a, b and c.
law GroupConfig.nodes_are_reached:
  for cfg: GroupConfig
  for g: List<&2, U32>
  for v: List<&2, U32>
  (
    {
      WordListSets.contains(GroupConfig.nodes(cfg, g), v) == True{}: Bool
    } -> Exists(List<&2, List<&2, U32>>, path => Reaches(cfg, g, path, v))
  )
    & (
      @path: List<
        &2,
        List<
          &2,
          U32>> -> Reaches(
        cfg,
        g,
        path,
        v
      ) -> {WordListSets.contains(GroupConfig.nodes(cfg, g), v) == True{}: Bool}
    )

# the answers a and b are the same
def EqualNames(a: List<&2, List<&2, U32>>, b: List<&2, List<&2, U32>>) -> Type:
  {a == b: List<&2, List<&2, U32>>}

# Means: with more ballots, the voters of a step only become known, or
# Contradicted; once known they never change.
# For free: every node that knows the voters of a step knows the same voters;
# the ballots of a step can be judged by voters that never change; a decision
# that rests on them stays a decision.
# For the goal: slot consensus needs fixed voters per step, and owner groups
# give them while the groups themselves change (Shape 4, Trust 3).
# Example: once root slot 3 is decided, the voters of root slot 4 are known on
# every node that holds those ballots, for good.
law voters_are_monotone:
  for ~decode: List<&2, U32> -> DecodedChoice
  for step: SlotConsensus.Step
  for root: List<&2, U32>
  for genesis: List<&2, GroupChange>
  for a: List<&2, SlotConsensus.Ballot>
  for b: List<&2, SlotConsensus.Ballot>
  SlotConsensus.Ballots.Grows(a, b)
    -> MonotoneQueries.MonotoneAnswer.Below(
      ~(List<&2, List<&2, U32>>),
      ~EqualNames,
      voters(~decode, step, root, genesis, a),
      voters(~decode, step, root, genesis, b)
    )

# Means: the eras of the slots of a line never go back: slot k+1 of a line is
# ruled by the configuration of the same era as slot k, or of a later one.
# For free: once a line's owners change, no later slot of the line goes back to
# the old ones; a change of a group reaches a line at the slot whose era is at
# or after the change, and every slot after it.
# For the goal: changing a group changes the owners of everything it owns, each
# by its next decided step that names a later era (Shape 4).
# Example: slot 4 of main is of era 9, so slot 5 of main is of era 9 or later.
law era_grows:
  for ~decode: List<&2, U32> -> DecodedChoice
  for k: Nat
  for l: List<&2, U32>
  for root: List<&2, U32>
  for genesis: List<&2, GroupChange>
  for all: List<&2, SlotConsensus.Ballot>
  for x: Nat
  for y: Nat
  {
    era(
      ~decode,
      k,
      l,
      root,
      genesis,
      all
    )
      == MonotoneQueries.Known{x}: MonotoneQueries.MonotoneAnswer<Nat>
  }
    -> {
      era(
        ~decode,
        1n+k,
        l,
        root,
        genesis,
        all
      )
        == MonotoneQueries.Known{y}: MonotoneQueries.MonotoneAnswer<Nat>
    }
    -> {Nat.is_le(x, y) == True{}: Bool}
