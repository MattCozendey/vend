import Base
import ../shared/shared.bend as Shared
import ./spec.bend as Spec

# Test b: our SHA-256 against the examples of the standard (FIPS 180-4), those
# whose message is a whole number of words. A type cannot say that a function
# is SHA-256, and a law compares our code only with our own definitions; only
# the standard's own values can check it.

# the words of the list r, each after a space
def FixedLengthList.show.after(n: Nat, r: Shared.FixedLengthList(U32, n)) -> String:
  match n:
    case 0n:
      ""
    case 1n+m:
      match r:
        case (w, rest):
          " " ++ U32.show(w) ++ FixedLengthList.show.after(m, rest)

# the words of the list r of 1 + m words, with a space between two words
def FixedLengthList.show(m: Nat, r: Shared.FixedLengthList(U32, 1n+m)) -> String:
  match r:
    case (w, rest):
      U32.show(w) ++ FixedLengthList.show.after(m, rest)

# the SHA-256 of three messages: "", the 448-bit message "abcdbcde...nopq", and
# the 896-bit message "abcdefgh...nopqrstu"
def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(FixedLengthList.show(7n, Spec.Sha256.of_words([])))
    IO.print(
      FixedLengthList.show(
        7n,
        Spec.Sha256.of_words(
          [
            1633837924,
            1650680933,
            1667523942,
            1684366951,
            1701209960,
            1718052969,
            1734895978,
            1751738987,
            1768581996,
            1785425005,
            1802268014,
            1819111023,
            1835954032,
            1852797041
          ]
        )
      )
    )
    IO.print(
      FixedLengthList.show(
        7n,
        Spec.Sha256.of_words(
          [
            1633837924,
            1701209960,
            1650680933,
            1718052969,
            1667523942,
            1734895978,
            1684366951,
            1751738987,
            1701209960,
            1768581996,
            1718052969,
            1785425005,
            1734895978,
            1802268014,
            1751738987,
            1819111023,
            1768581996,
            1835954032,
            1785425005,
            1852797041,
            1802268014,
            1869640050,
            1819111023,
            1886483059,
            1835954032,
            1903326068,
            1852797041,
            1920169077
          ]
        )
      )
    )

#| 3820012610 2566659092 2600203464 2574235940 665731556 1687917388 2761267483 2018687061
#| 613247585 3523623096 3854575251 205414457 2738676825 1694441831 4142722516 433784513
#| 3478853287 2024768384 57468318 2063897143 186948369 3908074065 2947302659 2063526353
