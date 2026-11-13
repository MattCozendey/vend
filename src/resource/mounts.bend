import Base
import ../shared/replica.bend as Replicas
import ../shared/shared/ledger.bend as Ledgers
import ../shared/shared/shared/shared/crit.bend as Crits
import ../shared/shared/shared/shared/shared.bend as Shared
import ../shared/vend.bend as Vend
import ../writer/requests.bend as Requests
import ./resources.bend as Resources

# Mounts
# ------

# the resources mounted to a node: the branch of each, by the key of its URI.
# A resource is mounted to one branch at a time: to mount it to another is a
# checkout, and to mount another resource to another branch is a worktree
def Mounts() -> Data:
  Crits.Dict(Vend.Branch)

# a node may stop: it is forced to, or no resource is mounted and no writer
# is connected
def Node.may_stop(mounts: Mounts(), writers: Crits.Dict(Unit), force: Bool) -> Bool:
  Bool.or(
    force,
    Bool.and(Crits.Dict.is_empty(Vend.Branch, mounts), Crits.Dict.is_empty(Unit, writers))
  )

# the change that records what a resource held when it is mounted: a write
# of the resource x since the newest version, when the branch does not hold
# it at its tip t (some none: nothing to record; none: l lacks a part, so a
# read cannot tell). The node keeps the bytes and the format of x before it
# asks
def Mount.change(
  ~d: Vend.Led(),
  +l: Vend.L(d),
  +t: Replicas.Tip,
  +n: Resources.Name,
  +x: Requests.Res
) -> Maybe<&2, Maybe<&2, Requests.Change>>:
  Maybe.bind(
    &2,
    Maybe<&2, Requests.Res>,
    Maybe<&2, Requests.Change>,
    Vend.Res.find(~d, l, Replicas.Tip.content(t), n),
    m => Maybe.map(
      &2,
      Maybe<&2, Ledgers.Id>,
      Maybe<&2, Requests.Change>,
      v => Shared.Maybe.when(
        Requests.Change,
        Bool.not(Vend.Res.same(m, Some{x})),
        u => Some{Requests.Change.Write{n, v, Requests.Content.New{x}}}
      ),
      Replicas.Tip.newest(~Requests.Ask.machine(), ~d, l, t)
    )
  )
