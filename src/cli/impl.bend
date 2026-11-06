import Base
import ../shared.bend as Shared
import ./spec.bend as Spec

# no True is False
def Bool.true_not_false(e: {True{} == False{}: Bool}) -> Empty:
  %e: Bool.pick(Type, _, Unit, Empty)
  Unit{}

def Spec.parse_after_show(root, rs, u, h, n):
  match rs:
    case Nil{}:
      Empty.absurd(
        {
          Spec.Cli.parse(
            Spec.Cli.show(Spec.Watch{root, []})
          )
            == Done{Spec.Watch{root, []}}: Result<&2, &2, String, Spec.Cmd>
        },
        Bool.true_not_false(n)
      )
    case Con{r, t}:
      %Equal.sym(Bool, Maybe.is_some(&2, Shared.Uri, Shared.Uri.read(root)), True{}, u):
        {
          Shared.Bool.when(
            Result<&2, &2, String, Spec.Cmd>,
            List.all.if(v => Spec.Cli.globs_read(Con{r, t}), _),
            w => Spec.Cli.watch.of(root, Con{r, t}),
            w => Fail{Spec.Cli.usage()}
          )
            == Done{Spec.Watch{root, Con{r, t}}}: Result<&2, &2, String, Spec.Cmd>
        }
      %Equal.sym(Bool, Spec.Cli.globs_read(Con{r, t}), True{}, h):
        {
          Shared.Bool.when(
            Result<&2, &2, String, Spec.Cmd>,
            _,
            w => Spec.Cli.watch.of(root, Con{r, t}),
            w => Fail{Spec.Cli.usage()}
          )
            == Done{Spec.Watch{root, Con{r, t}}}: Result<&2, &2, String, Spec.Cmd>
        }
      {==}
