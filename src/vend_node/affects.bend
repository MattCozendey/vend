import Base

# x is among xs
def In(xs: List<&2, String>, x: String) -> Data:
  {List.contains(~String, ~String.eq, xs, x) == True{}: Bool}

# test
def In.twice(xs: List<&2, String>, x: String, +h: In(xs, x)) -> In(xs, x) & In(xs, x):
  (h, h)

# test
def In.fn(xs: List<&2, String>, x: String) -> In(xs, x) -> {List.contains(~String, ~String.eq, xs, x) == True{}: Bool} & In(xs, x):
  +h => (h, h)
