import Base
import ../../../shared.bend as Shared

# Text and bytes
# --------------

# a resource's content: one byte per U32, as Base's File effects use; the
# bytes of a text are its UTF-8 (Bytes.of_text_bytes)
def Bytes() -> Data:
  List<&2, U32>

# no bit of w is set
def Word.is_zero(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      match w:
        case WCon{b, t}:
          List.all.if(u => Word.is_zero(p, t), Bool.not(b))

# every code of b is a byte: no bit above the eighth is set
def Bytes.is_bytes(b: List<&2, U32>) -> Bool:
  match b:
    case Nil{}:
      True{}
    case Con{U32{WCon{_, WCon{_, WCon{_, WCon{_, WCon{_, WCon{_, WCon{_, WCon{_, h}}}}}}}}}, r}:
      List.all.if(u => Bytes.is_bytes(r), Word.is_zero(24n, h))

# the byte of the bits b0 (the lowest) to b7
def Byte.of(b0: Bool, b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, b6: Bool, b7: Bool) -> U32:
  U32{
    WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, Word.zero(24n)}}}}}}}}
  }

# UTF-8
# -----
# A character of up to 7 bits is one byte; of up to 11, 16 or 21 bits, two,
# three or four. A character with a higher bit set is not Unicode: it gives the
# replacement character U+FFFD.

# the replacement character, U+FFFD
def Utf8.bad() -> Char:
  Chr{65533}

# c holds no bit above the 21st: UTF-8 has its bytes
def Char.fits_utf8(c: Char) -> Bool:
  match c:
    case Chr{
      U32{
        WCon{
          _,
          WCon{
            _,
            WCon{
              _,
              WCon{
                _,
                WCon{
                  _,
                  WCon{
                    _,
                    WCon{
                      _,
                      WCon{
                        _,
                        WCon{
                          _,
                          WCon{
                            _,
                            WCon{
                              _,
                              WCon{
                                _,
                                WCon{
                                  _,
                                  WCon{
                                    _,
                                    WCon{
                                      _,
                                      WCon{
                                        _,
                                        WCon{
                                          _,
                                          WCon{
                                            _,
                                            WCon{
                                              _,
                                              WCon{
                                                _,
                                                WCon{
                                                  _,
                                                  WCon{
                                                    b21,
                                                    WCon{
                                                      b22,
                                                      WCon{
                                                        b23,
                                                        WCon{
                                                          b24,
                                                          WCon{
                                                            b25,
                                                            WCon{
                                                              b26,
                                                              WCon{
                                                                b27,
                                                                WCon{
                                                                  b28,
                                                                  WCon{
                                                                    b29,
                                                                    WCon{b30, WCon{b31, WNil{}}}
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }:
      Bool.not(
        Bool.or(
          b31,
          Bool.or(
            b30,
            Bool.or(
              b29,
              Bool.or(
                b28,
                Bool.or(
                  b27,
                  Bool.or(b26, Bool.or(b25, Bool.or(b24, Bool.or(b23, Bool.or(b22, b21)))))
                )
              )
            )
          )
        )
      )

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only a law's premise calls it, so it never runs
# every character of s holds no bit above the 21st
def Text.fits_utf8(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, r}:
      Bool.and(Char.fits_utf8(c), Text.fits_utf8(r))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the bytes of a character of 8 to 11 bits, or of fewer (long)
def Utf8.two(
  long: Bool,
  b0: Bool,
  b1: Bool,
  b2: Bool,
  b3: Bool,
  b4: Bool,
  b5: Bool,
  b6: Bool,
  b7: Bool,
  b8: Bool,
  b9: Bool,
  b10: Bool
) -> List<&2, U32>:
  match long:
    case True{}:
      [
        Byte.of(b6, b7, b8, b9, b10, False{}, True{}, True{}),
        Byte.of(b0, b1, b2, b3, b4, b5, False{}, True{})
      ]
    case False{}:
      [Byte.of(b0, b1, b2, b3, b4, b5, b6, False{})]

# the bytes of a character of 12 to 16 bits, or of fewer (long)
def Utf8.three(
  long: Bool,
  b0: Bool,
  b1: Bool,
  b2: Bool,
  b3: Bool,
  b4: Bool,
  b5: Bool,
  b6: Bool,
  +b7: Bool,
  +b8: Bool,
  +b9: Bool,
  +b10: Bool,
  b11: Bool,
  b12: Bool,
  b13: Bool,
  b14: Bool,
  b15: Bool
) -> List<&2, U32>:
  match long:
    case True{}:
      [
        Byte.of(b12, b13, b14, b15, False{}, True{}, True{}, True{}),
        Byte.of(b6, b7, b8, b9, b10, b11, False{}, True{}),
        Byte.of(b0, b1, b2, b3, b4, b5, False{}, True{})
      ]
    case False{}:
      Utf8.two(
        Bool.or(b10, Bool.or(b9, Bool.or(b8, b7))),
        b0,
        b1,
        b2,
        b3,
        b4,
        b5,
        b6,
        b7,
        b8,
        b9,
        b10
      )

# the bytes of a character of 17 to 21 bits, or of fewer (long)
def Utf8.four(
  long: Bool,
  b0: Bool,
  b1: Bool,
  b2: Bool,
  b3: Bool,
  b4: Bool,
  b5: Bool,
  b6: Bool,
  b7: Bool,
  b8: Bool,
  b9: Bool,
  b10: Bool,
  +b11: Bool,
  +b12: Bool,
  +b13: Bool,
  +b14: Bool,
  +b15: Bool,
  b16: Bool,
  b17: Bool,
  b18: Bool,
  b19: Bool,
  b20: Bool
) -> List<&2, U32>:
  match long:
    case True{}:
      [
        Byte.of(b18, b19, b20, False{}, True{}, True{}, True{}, True{}),
        Byte.of(b12, b13, b14, b15, b16, b17, False{}, True{}),
        Byte.of(b6, b7, b8, b9, b10, b11, False{}, True{}),
        Byte.of(b0, b1, b2, b3, b4, b5, False{}, True{})
      ]
    case False{}:
      Utf8.three(
        Bool.or(b15, Bool.or(b14, Bool.or(b13, Bool.or(b12, b11)))),
        b0,
        b1,
        b2,
        b3,
        b4,
        b5,
        b6,
        b7,
        b8,
        b9,
        b10,
        b11,
        b12,
        b13,
        b14,
        b15
      )

# the bytes of a character of the bits b0 to b20, when no higher bit is set
# (over); else the bytes of the replacement character
def Utf8.fit(
  over: Bool,
  b0: Bool,
  b1: Bool,
  b2: Bool,
  b3: Bool,
  b4: Bool,
  b5: Bool,
  b6: Bool,
  b7: Bool,
  b8: Bool,
  b9: Bool,
  b10: Bool,
  b11: Bool,
  b12: Bool,
  b13: Bool,
  b14: Bool,
  b15: Bool,
  +b16: Bool,
  +b17: Bool,
  +b18: Bool,
  +b19: Bool,
  +b20: Bool
) -> List<&2, U32>:
  match over:
    case True{}:
      [
        Byte.of(True{}, True{}, True{}, True{}, False{}, True{}, True{}, True{}),
        Byte.of(True{}, True{}, True{}, True{}, True{}, True{}, False{}, True{}),
        Byte.of(True{}, False{}, True{}, True{}, True{}, True{}, False{}, True{})
      ]
    case False{}:
      Utf8.four(
        Bool.or(b20, Bool.or(b19, Bool.or(b18, Bool.or(b17, b16)))),
        b0,
        b1,
        b2,
        b3,
        b4,
        b5,
        b6,
        b7,
        b8,
        b9,
        b10,
        b11,
        b12,
        b13,
        b14,
        b15,
        b16,
        b17,
        b18,
        b19,
        b20
      )

# the UTF-8 bytes of c
def Utf8.char(c: Char) -> List<&2, U32>:
  match c:
    case Chr{
      U32{
        WCon{
          b0,
          WCon{
            b1,
            WCon{
              b2,
              WCon{
                b3,
                WCon{
                  b4,
                  WCon{
                    b5,
                    WCon{
                      b6,
                      WCon{
                        b7,
                        WCon{
                          b8,
                          WCon{
                            b9,
                            WCon{
                              b10,
                              WCon{
                                b11,
                                WCon{
                                  b12,
                                  WCon{
                                    b13,
                                    WCon{
                                      b14,
                                      WCon{
                                        b15,
                                        WCon{
                                          b16,
                                          WCon{
                                            b17,
                                            WCon{
                                              b18,
                                              WCon{
                                                b19,
                                                WCon{
                                                  b20,
                                                  WCon{
                                                    b21,
                                                    WCon{
                                                      b22,
                                                      WCon{
                                                        b23,
                                                        WCon{
                                                          b24,
                                                          WCon{
                                                            b25,
                                                            WCon{
                                                              b26,
                                                              WCon{
                                                                b27,
                                                                WCon{
                                                                  b28,
                                                                  WCon{
                                                                    b29,
                                                                    WCon{b30, WCon{b31, WNil{}}}
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }:
      Utf8.fit(
        Bool.or(
          b31,
          Bool.or(
            b30,
            Bool.or(
              b29,
              Bool.or(
                b28,
                Bool.or(
                  b27,
                  Bool.or(b26, Bool.or(b25, Bool.or(b24, Bool.or(b23, Bool.or(b22, b21)))))
                )
              )
            )
          )
        ),
        b0,
        b1,
        b2,
        b3,
        b4,
        b5,
        b6,
        b7,
        b8,
        b9,
        b10,
        b11,
        b12,
        b13,
        b14,
        b15,
        b16,
        b17,
        b18,
        b19,
        b20
      )

# the UTF-8 bytes of s
def Bytes.of_text(s: String) -> Bytes():
  match s:
    case SNil{}:
      []
    case SCon{c, r}:
      List.append(&2, U32, Utf8.char(c), Bytes.of_text(r))

# what a reader of UTF-8 bytes waits for: the start of a character, or need
# more bytes of a character whose bits so far are acc (the lowest first)
type Utf8.Wait is Data:
  Utf8.start{}
  Utf8.more{need: Nat, acc: List<&2, Bool>}

# what a byte gives the reader: what it waits for next, and the characters
# that the byte ends
type Utf8.Out is Data:
  Utf8.Out{wait: Utf8.Wait, chars: List<&2, Char>}

# what the reader waits for next, after o
def Utf8.Out.wait(o: Utf8.Out) -> Utf8.Wait:
  match o:
    case Utf8.Out{w, cs}:
      w

# the characters that o ends
def Utf8.Out.chars(o: Utf8.Out) -> List<&2, Char>:
  match o:
    case Utf8.Out{w, cs}:
      cs

# the n bits of bs (the lowest first), then unset bits
def Utf8.word(n: Nat, bs: List<&2, Bool>) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match bs:
        case Nil{}:
          WCon{False{}, Utf8.word(p, [])}
        case Con{h, t}:
          WCon{h, Utf8.word(p, t)}

# the character of the bits bs (the lowest first)
def Utf8.char_of(bs: List<&2, Bool>) -> Char:
  Chr{U32{Utf8.word(32n, bs)}}

# what the first byte of a character, of the bits x0 (the lowest) to x7, gives:
# the kind is in the bits 3 to 7, which a match reads in that order
def Utf8.lead(
  x0: Bool,
  x1: Bool,
  x2: Bool,
  x3: Bool,
  x4: Bool,
  x5: Bool,
  x6: Bool,
  x7: Bool
) -> Utf8.Out:
  match x3:
    case True{}:
      match x4:
        case True{}:
          match x5:
            case True{}:
              match x6:
                case True{}:
                  match x7:
                    case True{}:
                      Utf8.Out{Utf8.start{}, [Utf8.bad()]}
                    case False{}:
                      Utf8.Out{
                        Utf8.start{},
                        [Utf8.char_of([x0, x1, x2, True{}, True{}, True{}, True{}])]
                      }
                case False{}:
                  match x7:
                    case True{}:
                      Utf8.Out{Utf8.start{}, [Utf8.bad()]}
                    case False{}:
                      Utf8.Out{
                        Utf8.start{},
                        [Utf8.char_of([x0, x1, x2, True{}, True{}, True{}, False{}])]
                      }
            case False{}:
              match x6:
                case True{}:
                  match x7:
                    case True{}:
                      Utf8.Out{Utf8.more{1n, [x0, x1, x2, True{}, True{}]}, []}
                    case False{}:
                      Utf8.Out{
                        Utf8.start{},
                        [Utf8.char_of([x0, x1, x2, True{}, True{}, False{}, True{}])]
                      }
                case False{}:
                  match x7:
                    case True{}:
                      Utf8.Out{Utf8.start{}, [Utf8.bad()]}
                    case False{}:
                      Utf8.Out{
                        Utf8.start{},
                        [Utf8.char_of([x0, x1, x2, True{}, True{}, False{}, False{}])]
                      }
        case False{}:
          match x5:
            case True{}:
              match x6:
                case True{}:
                  match x7:
                    case True{}:
                      Utf8.Out{Utf8.more{2n, [x0, x1, x2, True{}]}, []}
                    case False{}:
                      Utf8.Out{
                        Utf8.start{},
                        [Utf8.char_of([x0, x1, x2, True{}, False{}, True{}, True{}])]
                      }
                case False{}:
                  match x7:
                    case True{}:
                      Utf8.Out{Utf8.start{}, [Utf8.bad()]}
                    case False{}:
                      Utf8.Out{
                        Utf8.start{},
                        [Utf8.char_of([x0, x1, x2, True{}, False{}, True{}, False{}])]
                      }
            case False{}:
              match x6:
                case True{}:
                  match x7:
                    case True{}:
                      Utf8.Out{Utf8.more{1n, [x0, x1, x2, True{}, False{}]}, []}
                    case False{}:
                      Utf8.Out{
                        Utf8.start{},
                        [Utf8.char_of([x0, x1, x2, True{}, False{}, False{}, True{}])]
                      }
                case False{}:
                  match x7:
                    case True{}:
                      Utf8.Out{Utf8.start{}, [Utf8.bad()]}
                    case False{}:
                      Utf8.Out{
                        Utf8.start{},
                        [Utf8.char_of([x0, x1, x2, True{}, False{}, False{}, False{}])]
                      }
    case False{}:
      match x4:
        case True{}:
          match x5:
            case True{}:
              match x6:
                case True{}:
                  match x7:
                    case True{}:
                      Utf8.Out{Utf8.more{3n, [x0, x1, x2]}, []}
                    case False{}:
                      Utf8.Out{
                        Utf8.start{},
                        [Utf8.char_of([x0, x1, x2, False{}, True{}, True{}, True{}])]
                      }
                case False{}:
                  match x7:
                    case True{}:
                      Utf8.Out{Utf8.start{}, [Utf8.bad()]}
                    case False{}:
                      Utf8.Out{
                        Utf8.start{},
                        [Utf8.char_of([x0, x1, x2, False{}, True{}, True{}, False{}])]
                      }
            case False{}:
              match x6:
                case True{}:
                  match x7:
                    case True{}:
                      Utf8.Out{Utf8.more{1n, [x0, x1, x2, False{}, True{}]}, []}
                    case False{}:
                      Utf8.Out{
                        Utf8.start{},
                        [Utf8.char_of([x0, x1, x2, False{}, True{}, False{}, True{}])]
                      }
                case False{}:
                  match x7:
                    case True{}:
                      Utf8.Out{Utf8.start{}, [Utf8.bad()]}
                    case False{}:
                      Utf8.Out{
                        Utf8.start{},
                        [Utf8.char_of([x0, x1, x2, False{}, True{}, False{}, False{}])]
                      }
        case False{}:
          match x5:
            case True{}:
              match x6:
                case True{}:
                  match x7:
                    case True{}:
                      Utf8.Out{Utf8.more{2n, [x0, x1, x2, False{}]}, []}
                    case False{}:
                      Utf8.Out{
                        Utf8.start{},
                        [Utf8.char_of([x0, x1, x2, False{}, False{}, True{}, True{}])]
                      }
                case False{}:
                  match x7:
                    case True{}:
                      Utf8.Out{Utf8.start{}, [Utf8.bad()]}
                    case False{}:
                      Utf8.Out{
                        Utf8.start{},
                        [Utf8.char_of([x0, x1, x2, False{}, False{}, True{}, False{}])]
                      }
            case False{}:
              match x6:
                case True{}:
                  match x7:
                    case True{}:
                      Utf8.Out{Utf8.more{1n, [x0, x1, x2, False{}, False{}]}, []}
                    case False{}:
                      Utf8.Out{
                        Utf8.start{},
                        [Utf8.char_of([x0, x1, x2, False{}, False{}, False{}, True{}])]
                      }
                case False{}:
                  match x7:
                    case True{}:
                      Utf8.Out{Utf8.start{}, [Utf8.bad()]}
                    case False{}:
                      Utf8.Out{
                        Utf8.start{},
                        [Utf8.char_of([x0, x1, x2, False{}, False{}, False{}, False{}])]
                      }

# the replacement character before what w and the characters cs gave
def Utf8.bad_then(p: Utf8.Out) -> Utf8.Out:
  match p:
    case Utf8.Out{w, cs}:
      Utf8.Out{w, Utf8.bad() <> cs}

# the next of need bytes of a character with the bits acc so far: a byte
# 10xxxxxx (k7, k6: its bits 7 and 6) gives 6 more bits; another byte cuts the
# character short
def Utf8.cont(
  k6: Bool,
  k7: Bool,
  need: Nat,
  acc: List<&2, Bool>,
  x0: Bool,
  x1: Bool,
  x2: Bool,
  x3: Bool,
  x4: Bool,
  x5: Bool,
  x6: Bool,
  x7: Bool
) -> Utf8.Out:
  match k6 k7:
    case False{} True{}:
      match need:
        case 1n+k:
          match k:
            case 0n:
              Utf8.Out{
                Utf8.start{},
                [Utf8.char_of(List.append(&2, Bool, [x0, x1, x2, x3, x4, x5], acc))]
              }
            case 1n+j:
              Utf8.Out{Utf8.more{k, List.append(&2, Bool, [x0, x1, x2, x3, x4, x5], acc)}, []}
        case 0n:
          Utf8.Out{Utf8.start{}, [Utf8.bad()]}
    case _ _:
      Utf8.bad_then(Utf8.lead(x0, x1, x2, x3, x4, x5, x6, x7))

# what the byte of the bits x0 to x7 gives, while the reader waits for w
def Utf8.step(
  w: Utf8.Wait,
  x0: Bool,
  x1: Bool,
  x2: Bool,
  x3: Bool,
  x4: Bool,
  x5: Bool,
  +x6: Bool,
  +x7: Bool
) -> Utf8.Out:
  match w:
    case Utf8.start{}:
      Utf8.lead(x0, x1, x2, x3, x4, x5, x6, x7)
    case Utf8.more{need, acc}:
      Utf8.cont(x6, x7, need, acc, x0, x1, x2, x3, x4, x5, x6, x7)

# the end of the bytes, while the reader waits for w
def Utf8.end(w: Utf8.Wait) -> String:
  match w:
    case Utf8.start{}:
      SNil{}
    case Utf8.more{need, acc}:
      SCon{Utf8.bad(), SNil{}}

# the characters cs, then t
def Utf8.emit(cs: List<&2, Char>, t: String) -> String:
  match cs:
    case Nil{}:
      t
    case Con{c, r}:
      SCon{c, Utf8.emit(r, t)}

# the text of the bytes b, read while waiting for w: a character cut short
# reads as the replacement character
def Utf8.read(b: List<&2, U32>, w: Utf8.Wait) -> String:
  match b:
    case Nil{}:
      Utf8.end(w)
    case Con{
      U32{WCon{x0, WCon{x1, WCon{x2, WCon{x3, WCon{x4, WCon{x5, WCon{x6, WCon{x7, _}}}}}}}}},
      r
    }:
      +o = Utf8.step(w, x0, x1, x2, x3, x4, x5, x6, x7)
      Utf8.emit(Utf8.Out.chars(o), Utf8.read(r, Utf8.Out.wait(o)))

# the text of the UTF-8 bytes b: a byte that starts no character, or a
# character cut short, reads as the replacement character
def Bytes.to_text(b: Bytes()) -> String:
  Utf8.read(b, Utf8.start{})

# the text of the bytes of c, then of the bytes b: c, then b read, when c
# holds no bit above the 21st (fits); else that text as it is
def Utf8.back(fits: Bool, c: Char, b: List<&2, U32>) -> String:
  match fits:
    case True{}:
      SCon{c, Bytes.to_text(b)}
    case False{}:
      Bytes.to_text(List.append(&2, U32, Utf8.char(c), b))

# the character of the bits b31 to b0, from the highest
def Char.of_bits(
  b31: Bool,
  b30: Bool,
  b29: Bool,
  b28: Bool,
  b27: Bool,
  b26: Bool,
  b25: Bool,
  b24: Bool,
  b23: Bool,
  b22: Bool,
  b21: Bool,
  b20: Bool,
  b19: Bool,
  b18: Bool,
  b17: Bool,
  b16: Bool,
  b15: Bool,
  b14: Bool,
  b13: Bool,
  b12: Bool,
  b11: Bool,
  b10: Bool,
  b9: Bool,
  b8: Bool,
  b7: Bool,
  b6: Bool,
  b5: Bool,
  b4: Bool,
  b3: Bool,
  b2: Bool,
  b1: Bool,
  b0: Bool
) -> Char:
  Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WCon{b8, WCon{b9, WCon{b10, WCon{b11, WCon{b12, WCon{b13, WCon{b14, WCon{b15, WCon{b16, WCon{b17, WCon{b18, WCon{b19, WCon{b20, WCon{b21, WCon{b22, WCon{b23, WCon{b24, WCon{b25, WCon{b26, WCon{b27, WCon{b28, WCon{b29, WCon{b30, WCon{b31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}

# the bytes of c, then the bytes b: they read back as c, then b read, when c
# holds no bit above the 21st; and they are bytes when b is
def Utf8.Char.Laws(c: Char, b: List<&2, U32>) -> Type:
  {
    Bytes.to_text(List.append(&2, U32, Utf8.char(c), b)) == Utf8.back(Char.fits_utf8(c), c, b): String
  }
    & {Bytes.is_bytes(List.append(&2, U32, Utf8.char(c), b)) == Bytes.is_bytes(b): Bool}

# Utf8.char_laws, with the bits of the character from the highest
def Utf8.char_laws.bits(
  b31: Bool,
  b30: Bool,
  b29: Bool,
  b28: Bool,
  b27: Bool,
  b26: Bool,
  b25: Bool,
  b24: Bool,
  b23: Bool,
  b22: Bool,
  b21: Bool,
  b20: Bool,
  b19: Bool,
  b18: Bool,
  b17: Bool,
  b16: Bool,
  b15: Bool,
  b14: Bool,
  b13: Bool,
  b12: Bool,
  b11: Bool,
  b10: Bool,
  b9: Bool,
  b8: Bool,
  b7: Bool,
  b6: Bool,
  b5: Bool,
  b4: Bool,
  b3: Bool,
  b2: Bool,
  b1: Bool,
  b0: Bool,
  b: List<&2, U32>
) -> Utf8.Char.Laws(Char.of_bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0), b):
  match b31:
    case True{}:
      ({==}, {==})
    case False{}:
      match b30:
        case True{}:
          ({==}, {==})
        case False{}:
          match b29:
            case True{}:
              ({==}, {==})
            case False{}:
              match b28:
                case True{}:
                  ({==}, {==})
                case False{}:
                  match b27:
                    case True{}:
                      ({==}, {==})
                    case False{}:
                      match b26:
                        case True{}:
                          ({==}, {==})
                        case False{}:
                          match b25:
                            case True{}:
                              ({==}, {==})
                            case False{}:
                              match b24:
                                case True{}:
                                  ({==}, {==})
                                case False{}:
                                  match b23:
                                    case True{}:
                                      ({==}, {==})
                                    case False{}:
                                      match b22:
                                        case True{}:
                                          ({==}, {==})
                                        case False{}:
                                          match b21:
                                            case True{}:
                                              ({==}, {==})
                                            case False{}:
                                              match b20:
                                                case True{}:
                                                  ({==}, {==})
                                                case False{}:
                                                  match b19:
                                                    case True{}:
                                                      ({==}, {==})
                                                    case False{}:
                                                      match b18:
                                                        case True{}:
                                                          ({==}, {==})
                                                        case False{}:
                                                          match b17:
                                                            case True{}:
                                                              ({==}, {==})
                                                            case False{}:
                                                              match b16:
                                                                case True{}:
                                                                  ({==}, {==})
                                                                case False{}:
                                                                  match b15:
                                                                    case True{}:
                                                                      ({==}, {==})
                                                                    case False{}:
                                                                      match b14:
                                                                        case True{}:
                                                                          ({==}, {==})
                                                                        case False{}:
                                                                          match b13:
                                                                            case True{}:
                                                                              ({==}, {==})
                                                                            case False{}:
                                                                              match b12:
                                                                                case True{}:
                                                                                  ({==}, {==})
                                                                                case False{}:
                                                                                  match b11:
                                                                                    case True{}:
                                                                                      ({==}, {==})
                                                                                    case False{}:
                                                                                      match b10:
                                                                                        case True{}:
                                                                                          match b9:
                                                                                            case True{}:
                                                                                              ({==}, {==})
                                                                                            case False{}:
                                                                                              ({==}, {==})
                                                                                        case False{}:
                                                                                          match b9:
                                                                                            case True{}:
                                                                                              ({==}, {==})
                                                                                            case False{}:
                                                                                              match b8:
                                                                                                case True{}:
                                                                                                  ({==}, {==})
                                                                                                case False{}:
                                                                                                  match b7:
                                                                                                    case True{}:
                                                                                                      ({==}, {==})
                                                                                                    case False{}:
                                                                                                      match b6:
                                                                                                        case True{}:
                                                                                                          match b5:
                                                                                                            case True{}:
                                                                                                              match b4:
                                                                                                                case True{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      ({==}, {==})
                                                                                                                    case False{}:
                                                                                                                      ({==}, {==})
                                                                                                                case False{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      ({==}, {==})
                                                                                                                    case False{}:
                                                                                                                      ({==}, {==})
                                                                                                            case False{}:
                                                                                                              match b4:
                                                                                                                case True{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      ({==}, {==})
                                                                                                                    case False{}:
                                                                                                                      ({==}, {==})
                                                                                                                case False{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      ({==}, {==})
                                                                                                                    case False{}:
                                                                                                                      ({==}, {==})
                                                                                                        case False{}:
                                                                                                          match b5:
                                                                                                            case True{}:
                                                                                                              match b4:
                                                                                                                case True{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      ({==}, {==})
                                                                                                                    case False{}:
                                                                                                                      ({==}, {==})
                                                                                                                case False{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      ({==}, {==})
                                                                                                                    case False{}:
                                                                                                                      ({==}, {==})
                                                                                                            case False{}:
                                                                                                              match b4:
                                                                                                                case True{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      ({==}, {==})
                                                                                                                    case False{}:
                                                                                                                      ({==}, {==})
                                                                                                                case False{}:
                                                                                                                  match b3:
                                                                                                                    case True{}:
                                                                                                                      ({==}, {==})
                                                                                                                    case False{}:
                                                                                                                      ({==}, {==})

# the bytes of a character, then the bytes b, read back as the character,
# then b read, when it fits; and they are bytes when b is
def Utf8.char_laws(c: Char, b: List<&2, U32>) -> Utf8.Char.Laws(c, b):
  match c:
    case Chr{
      U32{
        WCon{
          b0,
          WCon{
            b1,
            WCon{
              b2,
              WCon{
                b3,
                WCon{
                  b4,
                  WCon{
                    b5,
                    WCon{
                      b6,
                      WCon{
                        b7,
                        WCon{
                          b8,
                          WCon{
                            b9,
                            WCon{
                              b10,
                              WCon{
                                b11,
                                WCon{
                                  b12,
                                  WCon{
                                    b13,
                                    WCon{
                                      b14,
                                      WCon{
                                        b15,
                                        WCon{
                                          b16,
                                          WCon{
                                            b17,
                                            WCon{
                                              b18,
                                              WCon{
                                                b19,
                                                WCon{
                                                  b20,
                                                  WCon{
                                                    b21,
                                                    WCon{
                                                      b22,
                                                      WCon{
                                                        b23,
                                                        WCon{
                                                          b24,
                                                          WCon{
                                                            b25,
                                                            WCon{
                                                              b26,
                                                              WCon{
                                                                b27,
                                                                WCon{
                                                                  b28,
                                                                  WCon{
                                                                    b29,
                                                                    WCon{b30, WCon{b31, WNil{}}}
                                                                  }
                                                                }
                                                              }
                                                            }
                                                          }
                                                        }
                                                      }
                                                    }
                                                  }
                                                }
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    }:
      Utf8.char_laws.bits(b31, b30, b29, b28, b27, b26, b25, b24, b23, b22, b21, b20, b19, b18, b17, b16, b15, b14, b13, b12, b11, b10, b9, b8, b7, b6, b5, b4, b3, b2, b1, b0, b)

# the bytes of a character, then the bytes b, read back as the character, then
# b read, when the character holds no bit above the 21st
def Utf8.char_back(
  c: Char,
  b: List<&2, U32>
) -> {
  Bytes.to_text(List.append(&2, U32, Utf8.char(c), b)) == Utf8.back(Char.fits_utf8(c), c, b): String
}:
  Pair.fst(
    {
      Bytes.to_text(List.append(&2, U32, Utf8.char(c), b)) == Utf8.back(Char.fits_utf8(c), c, b): String
    },
    {Bytes.is_bytes(List.append(&2, U32, Utf8.char(c), b)) == Bytes.is_bytes(b): Bool},
    Utf8.char_laws(c, b)
  )

# a text of characters with no bit above the 21st reads back from its bytes
law Bytes.text_back:
  for s: String
  {Text.fits_utf8(s) == True{}: Bool} -> {Bytes.to_text(Bytes.of_text(s)) == s: String}

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Bytes.text_back(s):
  match s:
    case SNil{}:
      h => {==}
    case SCon{+c, +r}:
      +h =>
        %Equal.sym(
          String,
          Bytes.to_text(List.append(&2, U32, Utf8.char(c), Bytes.of_text(r))),
          Utf8.back(Char.fits_utf8(c), c, Bytes.of_text(r)),
          Utf8.char_back(c, Bytes.of_text(r))
        ): {_ == SCon{c, r}: String}
        %Equal.sym(
          Bool,
          Char.fits_utf8(c),
          True{},
          Shared.Bool.and_true_left(Char.fits_utf8(c), Text.fits_utf8(r))(h)
        ): {Utf8.back(_, c, Bytes.of_text(r)) == SCon{c, r}: String}
        %Equal.sym(
          String,
          Bytes.to_text(Bytes.of_text(r)),
          r,
          Bytes.text_back(r)(Shared.Bool.and_true_right(Char.fits_utf8(c), Text.fits_utf8(r))(h))
        ): {SCon{c, _} == SCon{c, r}: String}
        {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information


# the bytes of a character, then the bytes b, are bytes when b is
def Utf8.char_bytes(
  c: Char,
  b: List<&2, U32>
) -> {Bytes.is_bytes(List.append(&2, U32, Utf8.char(c), b)) == Bytes.is_bytes(b): Bool}:
  Pair.snd(
    {
      Bytes.to_text(List.append(&2, U32, Utf8.char(c), b)) == Utf8.back(Char.fits_utf8(c), c, b): String
    },
    {Bytes.is_bytes(List.append(&2, U32, Utf8.char(c), b)) == Bytes.is_bytes(b): Bool},
    Utf8.char_laws(c, b)
  )

# every code of the bytes of a text is a byte
law Bytes.of_text_bytes:
  for s: String
  {Bytes.is_bytes(Bytes.of_text(s)) == True{}: Bool}

def Bytes.of_text_bytes(s):
  match s:
    case SNil{}:
      {==}
    case SCon{c, +r}:
      %Equal.sym(
        Bool,
        Bytes.is_bytes(List.append(&2, U32, Utf8.char(c), Bytes.of_text(r))),
        Bytes.is_bytes(Bytes.of_text(r)),
        Utf8.char_bytes(c, Bytes.of_text(r))
      ): {_ == True{}: Bool}
      Bytes.of_text_bytes(r)

# Text
# ----

# A text cut in two at a character: what comes before it, and after it.
type Cut<-A: Data> is Data:
  Cut{before: A, after: A}
# the cut of c then a text, given the cut of that text
def Text.cut.on(c: Char, r: Maybe<&2, Cut<String>>) -> Maybe<&2, Cut<String>>:
  match r:
    case None{}:
      None{}
    case Some{Cut{b, a}}:
      Some{Cut{SCon{c, b}, a}}
# s cut at its first character with code x, or None when it has none
def Text.cut(s: String, +x: U32) -> Maybe<&2, Cut<String>>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, +t}:
      Shared.Bool.when(
        Maybe<&2, Cut<String>>,
        U32.is_eq(Char.to_u32(c), x),
        u => Some{Cut{SNil{}, t}},
        u => Text.cut.on(c, Text.cut(t, x))
      )
# s holds a character with code x
def Text.has(s: String, +x: U32) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      List.any.if(u => Text.has(t, x), U32.is_eq(Char.to_u32(c), x))

# the text before the cut
def Cut.before(-A: Data, c: Cut<A>) -> A:
  match c:
    case Cut{b, a}:
      b

# the text after the cut
def Cut.after(-A: Data, c: Cut<A>) -> A:
  match c:
    case Cut{b, a}:
      a

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# a text after "nothing more" is itself
def Text.drop_none(s: String) -> {String.drop(s, 0n) == s: String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

# a text with nothing after it is itself
def Text.append_none(a: String) -> {String.append(a, "") == a: String}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, t}:
      Equal.cong(String, String, z => SCon{c, z}, String.append(t, ""), t, Text.append_none(t))

# Text.cut_none at the first character c, by whether it has the code x (hit)
def Text.cut_none.at(
  hit: Bool,
  c: Char,
  t: String,
  x: U32,
  ih: {Text.has(t, x) == False{}: Bool} -> {Text.cut(t, x) == None{}: Maybe<&2, Cut<String>>}
) -> {
  U32.is_eq(Char.to_u32(c), x) == hit: Bool
} -> {
  List.any.if(u => Text.has(t, x), hit) == False{}: Bool
} -> {
  Shared.Bool.when(
    Maybe<&2, Cut<String>>,
    hit,
    u => Some{Cut{SNil{}, t}},
    u => Text.cut.on(c, Text.cut(t, x))
  )
    == None{}: Maybe<&2, Cut<String>>
}:
  match hit:
    case True{}:
      e => h => Empty.absurd(
        {Some{Cut{SNil{}, t}} == None{}: Maybe<&2, Cut<String>>},
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, h))
      )
    case False{}:
      e => h =>
        %Equal.sym(
          Maybe<&2, Cut<String>>,
          Text.cut(t, x),
          None{},
          ih(h)
        ): {Text.cut.on(c, _) == None{}: Maybe<&2, Cut<String>>}
        {==}

# a text without the code x has no cut at x
def Text.cut_none(
  s: String,
  +x: U32
) -> {Text.has(s, x) == False{}: Bool} -> {Text.cut(s, x) == None{}: Maybe<&2, Cut<String>>}:
  match s:
    case SNil{}:
      h => {==}
    case SCon{+c, +t}:
      Text.cut_none.at(U32.is_eq(Char.to_u32(c), x), c, t, x, Text.cut_none(t, x))({==})

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Text.cut_at at the first character h of a, by whether it has the code x (hit)
def Text.cut_at.at(
  hit: Bool,
  h: Char,
  t: String,
  c: Char,
  b: String,
  x: U32,
  ih: {
    Text.has(t, x) == False{}: Bool
  } -> {Text.cut(String.append(t, SCon{c, b}), x) == Some{Cut{t, b}}: Maybe<&2, Cut<String>>}
) -> {
  U32.is_eq(Char.to_u32(h), x) == hit: Bool
} -> {
  List.any.if(u => Text.has(t, x), hit) == False{}: Bool
} -> {
  Shared.Bool.when(
    Maybe<&2, Cut<String>>,
    hit,
    u => Some{Cut{SNil{}, String.append(t, SCon{c, b})}},
    u => Text.cut.on(h, Text.cut(String.append(t, SCon{c, b}), x))
  )
    == Some{Cut{SCon{h, t}, b}}: Maybe<&2, Cut<String>>
}:
  match hit:
    case True{}:
      e => hh => Empty.absurd(
        {
          Some{
            Cut{SNil{}, String.append(t, SCon{c, b})}
          }
            == Some{Cut{SCon{h, t}, b}}: Maybe<&2, Cut<String>>
        },
        Shared.Bool.false_ne_true(Equal.sym(Bool, True{}, False{}, hh))
      )
    case False{}:
      e => hh =>
        %Equal.sym(
          Maybe<&2, Cut<String>>,
          Text.cut(String.append(t, SCon{c, b}), x),
          Some{Cut{t, b}},
          ih(hh)
        ): {Text.cut.on(h, _) == Some{Cut{SCon{h, t}, b}}: Maybe<&2, Cut<String>>}
        {==}
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a text a without the code x, then a character c with it, then b, cuts into
# a and b
def Text.cut_at(
  a: String,
  +c: Char,
  +b: String,
  +x: U32
) -> {
  Text.has(a, x) == False{}: Bool
} -> {
  U32.is_eq(Char.to_u32(c), x) == True{}: Bool
} -> {Text.cut(String.append(a, SCon{c, b}), x) == Some{Cut{a, b}}: Maybe<&2, Cut<String>>}:
  match a:
    case SNil{}:
      ha => hc =>
        %Equal.sym(
          Bool,
          U32.is_eq(Char.to_u32(c), x),
          True{},
          hc
        ): {
          Shared.Bool.when(
            Maybe<&2, Cut<String>>,
            _,
            u => Some{Cut{SNil{}, b}},
            u => Text.cut.on(c, Text.cut(b, x))
          )
            == Some{Cut{SNil{}, b}}: Maybe<&2, Cut<String>>
        }
        {==}
    case SCon{+h, +t}:
      ha => +hc => Text.cut_at.at(
        U32.is_eq(Char.to_u32(h), x),
        h,
        t,
        c,
        b,
        x,
        hh => Text.cut_at(t, c, b, x)(hh)(hc)
      )({==})(ha)

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Text.cut_parts once the rest is cut: by what it held (m)
def Text.cut_parts.on(
  m: Maybe<&2, Cut<String>>,
  c: Char,
  t: String,
  x: U32,
  a: String,
  b: String,
  ih: @a2: String -> @b2: String -> {
    Text.cut(t, x) == Some{Cut{a2, b2}}: Maybe<&2, Cut<String>>
  } -> {t == String.append(a2, SCon{Chr{x}, b2}): String}
) -> {
  Text.cut(t, x) == m: Maybe<&2, Cut<String>>
} -> {
  Text.cut.on(c, m) == Some{Cut{a, b}}: Maybe<&2, Cut<String>>
} -> {SCon{c, t} == String.append(a, SCon{Chr{x}, b}): String}:
  match m:
    case None{}:
      e => h => Empty.absurd(
        {SCon{c, t} == String.append(a, SCon{Chr{x}, b}): String},
        Shared.Bool.false_ne_true(
          Equal.cong(
            Maybe<&2, Cut<String>>,
            Bool,
            z => Maybe.is_some(&2, Cut<String>, z),
            None{},
            Some{Cut{a, b}},
            h
          )
        )
      )
    case Some{Cut{a2, b2}}:
      e => +h =>
        %Equal.cong(
          Maybe<&2, Cut<String>>,
          String,
          z => Cut.before(String, Maybe.default(&2, Cut<String>, z, Cut{"", ""})),
          Some{Cut{SCon{c, a2}, b2}},
          Some{Cut{a, b}},
          h
        ): {SCon{c, t} == String.append(_, SCon{Chr{x}, b}): String}
        %Equal.cong(
          Maybe<&2, Cut<String>>,
          String,
          z => Cut.after(String, Maybe.default(&2, Cut<String>, z, Cut{"", ""})),
          Some{Cut{SCon{c, a2}, b2}},
          Some{Cut{a, b}},
          h
        ): {SCon{c, t} == String.append(SCon{c, a2}, SCon{Chr{x}, _}): String}
        Equal.cong(
          String,
          String,
          z => SCon{c, z},
          t,
          String.append(a2, SCon{Chr{x}, b2}),
          ih(a2)(b2)(e)
        )
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# a character whose code is x is the character x
def Text.cut_parts.chr(
  c: Char,
  t: String,
  x: U32
) -> {U32.is_eq(Char.to_u32(c), x) == True{}: Bool} -> {SCon{c, t} == SCon{Chr{x}, t}: String}:
  match c:
    case Chr{y}:
      e => Equal.cong(U32, String, z => SCon{Chr{z}, t}, y, x, Shared.U32.is_eq_sound(y, x)(e))
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# Text.cut_parts at the first character c, by whether it has the code x (hit)
def Text.cut_parts.at(
  hit: Bool,
  c: Char,
  +t: String,
  +x: U32,
  a: String,
  b: String,
  ih: @a2: String -> @b2: String -> {
    Text.cut(t, x) == Some{Cut{a2, b2}}: Maybe<&2, Cut<String>>
  } -> {t == String.append(a2, SCon{Chr{x}, b2}): String}
) -> {
  U32.is_eq(Char.to_u32(c), x) == hit: Bool
} -> {
  Shared.Bool.when(
    Maybe<&2, Cut<String>>,
    hit,
    u => Some{Cut{SNil{}, t}},
    u => Text.cut.on(c, Text.cut(t, x))
  )
    == Some{Cut{a, b}}: Maybe<&2, Cut<String>>
} -> {SCon{c, t} == String.append(a, SCon{Chr{x}, b}): String}:
  match hit:
    case True{}:
      +e => +h =>
        %Equal.cong(
          Maybe<&2, Cut<String>>,
          String,
          z => Cut.before(String, Maybe.default(&2, Cut<String>, z, Cut{"", ""})),
          Some{Cut{SNil{}, t}},
          Some{Cut{a, b}},
          h
        ): {SCon{c, t} == String.append(_, SCon{Chr{x}, b}): String}
        %Equal.cong(
          Maybe<&2, Cut<String>>,
          String,
          z => Cut.after(String, Maybe.default(&2, Cut<String>, z, Cut{"", ""})),
          Some{Cut{SNil{}, t}},
          Some{Cut{a, b}},
          h
        ): {SCon{c, t} == SCon{Chr{x}, _}: String}
        Text.cut_parts.chr(c, t, x)(e)
    case False{}:
      e => h => Text.cut_parts.on(Text.cut(t, x), c, t, x, a, b, ih)({==})(h)
# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning

# a text cut at the code x is what comes before, that character, and what
# comes after
def Text.cut_parts(
  s: String,
  +x: U32,
  a: String,
  b: String
) -> {
  Text.cut(s, x) == Some{Cut{a, b}}: Maybe<&2, Cut<String>>
} -> {s == String.append(a, SCon{Chr{x}, b}): String}:
  match s:
    case SNil{}:
      h => Empty.absurd(
        {SNil{} == String.append(a, SCon{Chr{x}, b}): String},
        Shared.Bool.false_ne_true(
          Equal.cong(
            Maybe<&2, Cut<String>>,
            Bool,
            z => Maybe.is_some(&2, Cut<String>, z),
            None{},
            Some{Cut{a, b}},
            h
          )
        )
      )
    case SCon{+c, +t}:
      Text.cut_parts.at(
        U32.is_eq(Char.to_u32(c), x),
        c,
        t,
        x,
        a,
        b,
        a2 => b2 => Text.cut_parts(t, x, a2, b2)
      )({==})
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# Parts
# -----
# Texts joined by a character, and a text cut back into them.

# texts cut at a character: the parts before each cut, and the rest after the
# last one
type Parts is Data:
  Parts{parts: List<&2, String>, rest: String}

# the texts ps, each then the character c, then last
def Text.join(ps: List<&2, String>, +c: Char, last: String) -> String:
  match ps:
    case Nil{}:
      last
    case Con{p, r}:
      String.append(p, SCon{c, Text.join(r, c, last)})

# bend-lint: expect-begin bend-lint-rules/performance/eager_branch@information -- only a law's premise calls it, so it never runs
# no text of ps holds a character with code x
def Text.lacks_all(ps: List<&2, String>, +x: U32) -> Bool:
  match ps:
    case Nil{}:
      True{}
    case Con{p, r}:
      Bool.and(Bool.not(Text.has(p, x)), Text.lacks_all(r, x))
# bend-lint: expect-end bend-lint-rules/performance/eager_branch@information

# the text b before a cut, then the parts and the rest after it (m)
def Text.cuts.put(b: String, m: Maybe<&2, Parts>) -> Maybe<&2, Parts>:
  match m:
    case None{}:
      None{}
    case Some{Parts{ps, r}}:
      Some{Parts{b <> ps, r}}

# the parts of a text cut once already (c), then cut n more times at the code
# x, and the rest
def Text.cuts.of(n: Nat, c: Maybe<&2, Cut<String>>, +x: U32) -> Maybe<&2, Parts>:
  match n c:
    case _ None{}:
      None{}
    case 0n Some{Cut{b, a}}:
      Some{Parts{[b], a}}
    case 1n+k Some{Cut{b, a}}:
      Text.cuts.put(b, Text.cuts.of(k, Text.cut(a, x), x))

# the first n parts of s cut at the code x, and the rest; None when s holds
# fewer than n
def Text.cuts(n: Nat, s: String, +x: U32) -> Maybe<&2, Parts>:
  match n:
    case 0n:
      Some{Parts{[], s}}
    case 1n+k:
      Text.cuts.of(k, Text.cut(s, x), x)

# a text cut once already into b and a, then cut n more times, is b before
# the cuts of a
def Text.cuts.of_cut(
  +n: Nat,
  b: String,
  a: String,
  x: U32
) -> {
  Text.cuts.of(n, Some{Cut{b, a}}, x) == Text.cuts.put(b, Text.cuts(n, a, x)): Maybe<&2, Parts>
}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      {==}

# texts joined by c cut back at c into them and the last text, when no text
# but the last holds c
law Text.cuts_after_join:
  for ps: List<&2, String>
  for c: Char
  for last: String
  {Text.lacks_all(ps, Char.to_u32(c)) == True{}: Bool}
    -> {
      Text.cuts(
        List.length(&2, String, ps),
        Text.join(ps, c, last),
        Char.to_u32(c)
      )
        == Some{Parts{ps, last}}: Maybe<&2, Parts>
    }

# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
def Text.cuts_after_join(ps, c, last):
  match ps:
    case Nil{}:
      h => {==}
    case Con{+p, +r}:
      +c = c
      +last = last
      +h =>
        %Equal.sym(
          Maybe<&2, Cut<String>>,
          Text.cut(String.append(p, SCon{c, Text.join(r, c, last)}), Char.to_u32(c)),
          Some{Cut{p, Text.join(r, c, last)}},
          Text.cut_at(
            p,
            c,
            Text.join(r, c, last),
            Char.to_u32(c)
          )(
            Shared.Bool.not_true(
              Text.has(p, Char.to_u32(c))
            )(
              Shared.Bool.and_true_left(
                Bool.not(Text.has(p, Char.to_u32(c))),
                Text.lacks_all(r, Char.to_u32(c))
              )(h)
            )
          )(Shared.U32.is_eq_refl(Char.to_u32(c)))
        ): {
          Text.cuts.of(
            List.length(&2, String, r),
            _,
            Char.to_u32(c)
          )
            == Some{Parts{p <> r, last}}: Maybe<&2, Parts>
        }
        %Equal.sym(
          Maybe<&2, Parts>,
          Text.cuts.of(
            List.length(&2, String, r),
            Some{Cut{p, Text.join(r, c, last)}},
            Char.to_u32(c)
          ),
          Text.cuts.put(
            p,
            Text.cuts(List.length(&2, String, r), Text.join(r, c, last), Char.to_u32(c))
          ),
          Text.cuts.of_cut(List.length(&2, String, r), p, Text.join(r, c, last), Char.to_u32(c))
        ): {_ == Some{Parts{p <> r, last}}: Maybe<&2, Parts>}
        %Equal.sym(
          Maybe<&2, Parts>,
          Text.cuts(List.length(&2, String, r), Text.join(r, c, last), Char.to_u32(c)),
          Some{Parts{r, last}},
          Text.cuts_after_join(
            r,
            c,
            last
          )(
            Shared.Bool.and_true_right(
              Bool.not(Text.has(p, Char.to_u32(c))),
              Text.lacks_all(r, Char.to_u32(c))
            )(h)
          )
        ): {Text.cuts.put(p, _) == Some{Parts{p <> r, last}}: Maybe<&2, Parts>}
        {==}
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information

# bend-lint: expect-begin bend-lint-rules/language/reused_binder@warning -- in these proofs a second use sits in a rewrite motive or an erased argument; the checker accepts it
# bend-lint: expect-begin bend-lint-rules/performance/unused_result@information -- these binders are premises of a proof's own type; a proof does not run
# String.order.go of a string with itself, from EQ, is EQ
def String.order_refl(a: String) -> {String.order.go(a, a, EQ{}) == EQ{}: Cmp}:
  match a:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{x}:
          %Equal.sym(
            Cmp,
            U32.cmp(x, x),
            EQ{},
            Shared.U32.cmp_refl(x)
          ): {String.order.go(t, t, _) == EQ{}: Cmp}
          String.order_refl(t)
# String.order.go from c is c, then the order from EQ
def String.order_then(
  c: Cmp,
  a: String,
  b: String
) -> {String.order.go(a, b, c) == Shared.Cmp.then(c, String.order.go(a, b, EQ{})): Cmp}:
  match c a b:
    case EQ{} x y:
      {==}
    case LT{} SNil{} SNil{}:
      {==}
    case LT{} SNil{} SCon{y, t}:
      {==}
    case LT{} SCon{x, t} SNil{}:
      {==}
    case LT{} SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}
    case GT{} SNil{} SNil{}:
      {==}
    case GT{} SNil{} SCon{y, t}:
      {==}
    case GT{} SCon{x, t} SNil{}:
      {==}
    case GT{} SCon{Chr{x}, t1} SCon{Chr{y}, t2}:
      {==}

# String.order.go ends at EQ only if it started at EQ
def String.order_keeps(
  +c: Cmp,
  +a: String,
  +b: String
) -> {String.order.go(a, b, c) == EQ{}: Cmp} -> {c == EQ{}: Cmp}:
  h => Shared.Cmp.then_eq_left(
    c,
    String.order.go(a, b, EQ{})
  )(
    Equal.trans(
      Cmp,
      Shared.Cmp.then(c, String.order.go(a, b, EQ{})),
      String.order.go(a, b, c),
      EQ{},
      Equal.sym(
        Cmp,
        String.order.go(a, b, c),
        Shared.Cmp.then(c, String.order.go(a, b, EQ{})),
        String.order_then(c, a, b)
      ),
      h
    )
  )
# String.order.go from c is String.order.go from EQ, when c is EQ
def String.order_at(
  -c: Cmp,
  -t1: String,
  -t2: String,
  e: {c == EQ{}: Cmp}
) -> {String.order.go(t1, t2, c) == EQ{}: Cmp} -> {String.order.go(t1, t2, EQ{}) == EQ{}: Cmp}:
  %e: {String.order.go(t1, t2, c) == EQ{}: Cmp} -> {String.order.go(t1, t2, _) == EQ{}: Cmp}
  h => h
# String.order.go from EQ ends at EQ only for equal strings
def String.order_sound(
  a: String,
  b: String
) -> {String.order.go(a, b, EQ{}) == EQ{}: Cmp} -> {a == b: String}:
  match a b:
    case SNil{} SNil{}:
      _ => {==}
    case SNil{} SCon{y, t2}:
      h => Empty.absurd({SNil{} == SCon{y, t2}: String}, Shared.Cmp.ne_eq(LT{}, Unit{}, h))
    case SCon{x, t1} SNil{}:
      h => Empty.absurd({SCon{x, t1} == SNil{}: String}, Shared.Cmp.ne_eq(GT{}, Unit{}, h))
    case SCon{Chr{U32{+w1}}, +t1} SCon{Chr{U32{+w2}}, +t2}:
      +h =>
        +e = String.order_keeps(Word.cmp(32n, w1, w2), t1, t2)(h)
        h2 = String.order_at(Word.cmp(32n, w1, w2), t1, t2, e)(h)
        %Shared.Word.cmp_eq(
          32n,
          w1,
          w2
        )(e): {SCon{Chr{U32{w1}}, t1} == SCon{Chr{U32{_}}, t2}: String}
        %String.order_sound(t1, t2)(h2): {SCon{Chr{U32{w1}}, t1} == SCon{Chr{U32{w1}}, _}: String}
        {==}
# every string equals itself
def String.eq_refl(a: String) -> {String.eq(a, a) == True{}: Bool}:
  %Equal.sym(
    Cmp,
    String.order.go(a, a, EQ{}),
    EQ{},
    String.order_refl(a)
  ): {Cmp.is_eq(_) == True{}: Bool}
  {==}
# String.eq is True only for equal strings
def String.eq_sound(
  +a: String,
  +b: String
) -> {String.eq(a, b) == True{}: Bool} -> {a == b: String}:
  h => String.order_sound(a, b)(Shared.Cmp.is_eq_sound(String.order.go(a, b, EQ{}))(h))

# bend-lint: expect-end bend-lint-rules/language/reused_binder@warning
# bend-lint: expect-end bend-lint-rules/performance/unused_result@information
