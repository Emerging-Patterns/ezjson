# word characters between tokens make a word
import Base
import ../../src/lex.bend as Lex
import ./ArrayLength.bend as M1
import ./LexemeOrder.bend as M2
import ./WellFormedCells.bend as M3

# WP-L2, words: every character of a JSON number is a word character

# a character past all of classify's tests, with each test named: when a
# predicate holds of it and of none of the tested code points
law cls_other:
  for b91: Bool
  for b93: Bool
  for b123: Bool
  for b125: Bool
  for b58: Bool
  for b44: Bool
  for b34: Bool
  for b92: Bool
  for b32: Bool
  for b10: Bool
  for b13: Bool
  for b9: Bool
  for +cp: U32
  for pp: U32 -> Bool
  for e91: {U32.is_eq(cp, 91) == b91 : Bool}
  for e93: {U32.is_eq(cp, 93) == b93 : Bool}
  for e123: {U32.is_eq(cp, 123) == b123 : Bool}
  for e125: {U32.is_eq(cp, 125) == b125 : Bool}
  for e58: {U32.is_eq(cp, 58) == b58 : Bool}
  for e44: {U32.is_eq(cp, 44) == b44 : Bool}
  for e34: {U32.is_eq(cp, 34) == b34 : Bool}
  for e92: {U32.is_eq(cp, 92) == b92 : Bool}
  for e32: {U32.is_eq(cp, 32) == b32 : Bool}
  for e10: {U32.is_eq(cp, 10) == b10 : Bool}
  for e13: {U32.is_eq(cp, 13) == b13 : Bool}
  for e9: {U32.is_eq(cp, 9) == b9 : Bool}
  for h: {pp(cp) == True{} : Bool}
  for n91: {pp(91) == False{} : Bool}
  for n93: {pp(93) == False{} : Bool}
  for n123: {pp(123) == False{} : Bool}
  for n125: {pp(125) == False{} : Bool}
  for n58: {pp(58) == False{} : Bool}
  for n44: {pp(44) == False{} : Bool}
  for n34: {pp(34) == False{} : Bool}
  for n92: {pp(92) == False{} : Bool}
  for n32: {pp(32) == False{} : Bool}
  for n10: {pp(10) == False{} : Bool}
  for n13: {pp(13) == False{} : Bool}
  for n9: {pp(9) == False{} : Bool}
  {Bool.pick(Lex.Class, b91, Lex.CPunct{Lex.TOpenArr{}}, Bool.pick(Lex.Class, b93, Lex.CPunct{Lex.TCloseArr{}},
    Bool.pick(Lex.Class, b123, Lex.CPunct{Lex.TOpenObj{}}, Bool.pick(Lex.Class, b125, Lex.CPunct{Lex.TCloseObj{}},
    Bool.pick(Lex.Class, b58, Lex.CPunct{Lex.TColon{}}, Bool.pick(Lex.Class, b44, Lex.CPunct{Lex.TComma{}},
    Bool.pick(Lex.Class, b34, Lex.CQuote{}, Bool.pick(Lex.Class, b92, Lex.CBack{}, Bool.pick(Lex.Class, b32,
    Lex.CSpace{}, Bool.pick(Lex.Class, b10, Lex.CSpace{}, Bool.pick(Lex.Class, b13, Lex.CSpace{}, Bool.pick(Lex.Class,
    b9, Lex.CSpace{}, Lex.COther{})))))))))))) == Lex.COther{} : Lex.Class}

def cls_other(
  b91,
  b93,
  b123,
  b125,
  b58,
  b44,
  b34,
  b92,
  b32,
  b10,
  b13,
  b9,
  cp,
  pp,
  e91,
  e93,
  e123,
  e125,
  e58,
  e44,
  e34,
  e92,
  e32,
  e10,
  e13,
  e9,
  h,
  n91,
  n93,
  n123,
  n125,
  n58,
  n44,
  n34,
  n92,
  n32,
  n10,
  n13,
  n9
):
  match b91:
    case True{}:
      Empty.absurd({Lex.CPunct{Lex.TOpenArr{}} == Lex.COther{} : Lex.Class}, M1.true_false(Equal.trans(Bool, True{},
        pp(cp), False{},
        Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(91), False{},
          Equal.cong(U32, Bool, pp, cp, 91, M3.ueq(cp, 91, e91)), n91))))
    case False{}:
      match b93:
        case True{}:
          Empty.absurd({Lex.CPunct{Lex.TCloseArr{}} == Lex.COther{} : Lex.Class}, M1.true_false(Equal.trans(Bool,
              True{},
            pp(cp), False{},
            Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(93), False{},
              Equal.cong(U32, Bool, pp, cp, 93, M3.ueq(cp, 93, e93)), n93))))
        case False{}:
          match b123:
            case True{}:
              Empty.absurd({Lex.CPunct{Lex.TOpenObj{}} == Lex.COther{} : Lex.Class}, M1.true_false(Equal.trans(Bool,
                True{}, pp(cp), False{},
                Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(123), False{},
                  Equal.cong(U32, Bool, pp, cp, 123, M3.ueq(cp, 123, e123)), n123))))
            case False{}:
              match b125:
                case True{}:
                  Empty.absurd({Lex.CPunct{Lex.TCloseObj{}} == Lex.COther{} : Lex.Class},
                      M1.true_false(Equal.trans(Bool,
                    True{}, pp(cp), False{},
                    Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(125), False{},
                      Equal.cong(U32, Bool, pp, cp, 125, M3.ueq(cp, 125, e125)), n125))))
                case False{}:
                  match b58:
                    case True{}:
                      Empty.absurd({Lex.CPunct{Lex.TColon{}} == Lex.COther{} : Lex.Class},
                          M1.true_false(Equal.trans(Bool,
                        True{}, pp(cp), False{},
                        Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(58), False{},
                          Equal.cong(U32, Bool, pp, cp, 58, M3.ueq(cp, 58, e58)), n58))))
                    case False{}:
                      match b44:
                        case True{}:
                          Empty.absurd({Lex.CPunct{Lex.TComma{}} == Lex.COther{} : Lex.Class},
                            M1.true_false(Equal.trans(Bool, True{}, pp(cp), False{},
                            Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(44), False{},
                              Equal.cong(U32, Bool, pp, cp, 44, M3.ueq(cp, 44, e44)), n44))))
                        case False{}:
                          match b34:
                            case True{}:
                              Empty.absurd({Lex.CQuote{} == Lex.COther{} : Lex.Class}, M1.true_false(Equal.trans(Bool,
                                True{}, pp(cp), False{},
                                Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(34), False{},
                                  Equal.cong(U32, Bool, pp, cp, 34, M3.ueq(cp, 34, e34)), n34))))
                            case False{}:
                              match b92:
                                case True{}:
                                  Empty.absurd({Lex.CBack{} == Lex.COther{} : Lex.Class},
                                      M1.true_false(Equal.trans(Bool,
                                    True{}, pp(cp), False{},
                                    Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(92), False{},
                                      Equal.cong(U32, Bool, pp, cp, 92, M3.ueq(cp, 92, e92)), n92))))
                                case False{}:
                                  match b32:
                                    case True{}:
                                      Empty.absurd({Lex.CSpace{} == Lex.COther{} : Lex.Class},
                                        M1.true_false(Equal.trans(Bool, True{}, pp(cp), False{},
                                        Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(32), False{},
                                          Equal.cong(U32, Bool, pp, cp, 32, M3.ueq(cp, 32, e32)), n32))))
                                    case False{}:
                                      match b10:
                                        case True{}:
                                          Empty.absurd({Lex.CSpace{} == Lex.COther{} : Lex.Class},
                                            M1.true_false(Equal.trans(Bool, True{}, pp(cp), False{},
                                            Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(10),
                                              False{},
                                              Equal.cong(U32, Bool, pp, cp, 10, M3.ueq(cp, 10, e10)), n10))))
                                        case False{}:
                                          match b13:
                                            case True{}:
                                              Empty.absurd({Lex.CSpace{} == Lex.COther{} : Lex.Class},
                                                M1.true_false(Equal.trans(Bool, True{}, pp(cp), False{},
                                                Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp), pp(13),
                                                  False{},
                                                  Equal.cong(U32, Bool, pp, cp, 13, M3.ueq(cp, 13, e13)), n13))))
                                            case False{}:
                                              match b9:
                                                case True{}:
                                                  Empty.absurd({Lex.CSpace{} == Lex.COther{} : Lex.Class},
                                                    M1.true_false(Equal.trans(Bool, True{}, pp(cp), False{},
                                                    Equal.sym(Bool, pp(cp), True{}, h), Equal.trans(Bool, pp(cp),
                                                      pp(9), False{},
                                                      Equal.cong(U32, Bool, pp, cp, 9, M3.ueq(cp, 9, e9)), n9))))
                                                case False{}:
                                                  {==}

# a character a predicate holds of, where it holds of none of classify's code
# points, is a word character
law cls_by:
  for +ch: Char
  for pp: U32 -> Bool
  for h: {pp(Char.to_u32(ch)) == True{} : Bool}
  for n91: {pp(91) == False{} : Bool}
  for n93: {pp(93) == False{} : Bool}
  for n123: {pp(123) == False{} : Bool}
  for n125: {pp(125) == False{} : Bool}
  for n58: {pp(58) == False{} : Bool}
  for n44: {pp(44) == False{} : Bool}
  for n34: {pp(34) == False{} : Bool}
  for n92: {pp(92) == False{} : Bool}
  for n32: {pp(32) == False{} : Bool}
  for n10: {pp(10) == False{} : Bool}
  for n13: {pp(13) == False{} : Bool}
  for n9: {pp(9) == False{} : Bool}
  {Lex.classify(ch) == Lex.COther{} : Lex.Class}

def cls_by(ch, pp, h, n91, n93, n123, n125, n58, n44, n34, n92, n32, n10, n13, n9):
  +cp = Char.to_u32(ch)
  cls_other(U32.is_eq(cp, 91), U32.is_eq(cp, 93), U32.is_eq(cp, 123), U32.is_eq(cp, 125), U32.is_eq(cp, 58),
    U32.is_eq(cp, 44), U32.is_eq(cp, 34), U32.is_eq(cp, 92), U32.is_eq(cp, 32), U32.is_eq(cp, 10), U32.is_eq(cp,
    13), U32.is_eq(cp, 9),
    cp, pp, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, h, n91, n93, n123, n125, n58, n44,
      n34, n92, n32, n10, n13, n9)

# every character is a word character
def others(cs: List<&2, Char>) -> Type:
  match cs:
    case Nil{}:
      Unit
    case Con{hd, tl}:
      ({Lex.classify(hd) == Lex.COther{} : Lex.Class} & others(tl))

# a word's characters, fed in Word mode, are pushed onto the buffer
law run_word:
  for +cs: List<&2, Char>
  for hw: others(cs)
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {Lex.run(cs, Lex.Lex{Lex.Word{}, buf, toks}) ==
    Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, cs, buf), toks} : Lex.Lex}

def run_word(cs, hw, buf, toks):
  match cs:
    case Nil{}:
      {==}
    case Con{+hd, +tl}:
      (hc, ht) = hw
      Equal.trans(Lex.Lex, Lex.run(tl, Lex.feed(hd, Lex.Lex{Lex.Word{}, buf, toks})),
        Lex.run(tl, Lex.Lex{Lex.Word{}, hd <> buf, toks}), Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, tl,
          hd <> buf), toks},
        Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(tl, xx), Lex.feed(hd, Lex.Lex{Lex.Word{}, buf, toks}),
          Lex.Lex{Lex.Word{}, hd <> buf, toks}, M2.feed_as(hd, Lex.Word{}, buf, toks, Lex.COther{}, hc)),
        run_word(tl, ht, hd <> buf, toks))

# word characters, from between tokens, make a word
law lex_word:
  for +hd: Char
  for +tl: List<&2, Char>
  for hw: others(hd <> tl)
  for +toks: List<&2, Lex.Tok>
  {Lex.run(hd <> tl, Lex.Lex{Lex.Idle{}, [], toks}) ==
    Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, hd <> tl, []), toks} : Lex.Lex}

def lex_word(hd, tl, hw, toks):
  (hc, ht) = hw
  Equal.trans(Lex.Lex, Lex.run(tl, Lex.feed(hd, Lex.Lex{Lex.Idle{}, [], toks})),
    Lex.run(tl, Lex.Lex{Lex.Word{}, [hd], toks}), Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, tl, [hd]), toks},
    Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(tl, xx), Lex.feed(hd, Lex.Lex{Lex.Idle{}, [], toks}),
      Lex.Lex{Lex.Word{}, [hd], toks}, M2.feed_as(hd, Lex.Idle{}, [], toks, Lex.COther{}, hc)),
    run_word(tl, ht, [hd], toks))
