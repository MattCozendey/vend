import Base

# an answer that crossed IO, or why it did not
type Reply<a, -A: Kind(a)> is Kind(a):
  Reply.Delivered{answer: A}
  Reply.TimedOut{}
  Reply.Unreachable{}
