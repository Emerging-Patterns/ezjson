# the character lexer on printed text: escapes, controls, quotes, values
import Base
import ../../src/value.bend as V
import ../../src/lex.bend as Lex
import ../../src/print.bend as Print
import ../../laws/NumOkIsNumberRule.bend as L1
import ../../laws/defs/CursorAndNumberRules.bend as D1
import ./ArrayLength.bend as M1
import ./DenseTokens.bend as M2
import ./LexemeOrder.bend as M3
import ./LexerPunctuation.bend as M4
import ./NumberDigits.bend as M5
import ./StringTokens.bend as M6
import ./WellFormedCells.bend as M7

# what lex_ctl says of a code point: its \u00XX escape reads back as itself
def ctl_goal(uu: U32, buf: List<&2, Char>, toks: List<&2, Lex.Tok>) -> Type:
  {Lex.run(String.to_list(Print.escape.u(uu)), Lex.Lex{Lex.Str{}, buf, toks}) ==
    Lex.Lex{Lex.Str{}, Chr{uu} <> buf, toks} : Lex.Lex}

# a control's \u00XX escape, one control at a time
law lex_ctl5:
  for b0: Bool
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for b4: Bool
  for buf: List<&2, Char>
  for toks: List<&2, Lex.Tok>
  {Lex.run(String.to_list(Print.escape.u(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{},
    M7.zw(26n)}}}}}}})),
    Lex.Lex{Lex.Str{}, buf, toks}) ==
    Lex.Lex{Lex.Str{}, Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, M7.zw(26n)}}}}}}}} <> buf,
      toks} : Lex.Lex}

def lex_ctl5(b0, b1, b2, b3, b4, _buf, _toks):
  match b0 b1 b2 b3 b4:
    case False{} False{} False{} False{} False{}:
      {==}
    case False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} True{} True{}:
      {==}
    case False{} True{} False{} False{} False{}:
      {==}
    case False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} True{} True{}:
      {==}
    case True{} False{} False{} False{} False{}:
      {==}
    case True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} True{} True{}:
      {==}
    case True{} True{} False{} False{} False{}:
      {==}
    case True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} True{} True{}:
      {==}

# the control case, once bit 5 and the bits above are known
law lex_ctl.at:
  for cc: Cmp
  for b5: Bool
  for b0: Bool
  for b1: Bool
  for b2: Bool
  for b3: Bool
  for b4: Bool
  for +rest: Word(26n)
  for ec: {Word.cmp(26n, rest, M7.zw(26n)) == cc : Cmp}
  for h_lt: {Cmp.is_lt(Word.cmp.fin(b5, True{}, cc)) == True{} : Bool}
  for buf: List<&2, Char>
  for toks: List<&2, Lex.Tok>
  {Lex.run(String.to_list(Print.escape.u(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}})),
    Lex.Lex{Lex.Str{}, buf, toks}) ==
    Lex.Lex{Lex.Str{}, Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}} <> buf,
      toks} : Lex.Lex}

def lex_ctl.at(cc, b5, b0, b1, b2, b3, b4, rest, ec, h_lt, buf, toks):
  match cc:
    case LT{}:
      ez = Equal.cong(Cmp, Bool, xx => Cmp.is_lt(xx), Word.cmp(26n, rest, M7.zw(26n)), LT{}, ec)
      Empty.absurd(ctl_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}, buf, toks),
        M1.true_false(Equal.trans(Bool, True{}, Cmp.is_lt(Word.cmp(26n, rest, M7.zw(26n))), False{},
        Equal.sym(Bool, Cmp.is_lt(Word.cmp(26n, rest, M7.zw(26n))), True{}, ez), M7.zw_nlt(26n, rest))))
    case GT{}:
      match b5:
        case False{}:
          Empty.absurd(ctl_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}, buf, toks),
            M3.false_true(h_lt))
        case True{}:
          Empty.absurd(ctl_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}, buf, toks),
            M3.false_true(h_lt))
    case EQ{}:
      match b5:
        case True{}:
          Empty.absurd(ctl_goal(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, rest}}}}}}}, buf, toks),
            M3.false_true(h_lt))
        case False{}:
          er = Equal.sym(Word(26n), rest, M7.zw(26n),
            M7.weq(26n, rest, M7.zw(26n), Equal.cong(Cmp, Bool, xx => Cmp.is_eq(xx), Word.cmp(26n, rest, M7.zw(26n)),
                EQ{}, ec)))
          %er : {Lex.run(String.to_list(Print.escape.u(U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{},
            _}}}}}}})), Lex.Lex{Lex.Str{}, buf, toks}) ==
            Lex.Lex{Lex.Str{}, Chr{U32{WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{False{}, _}}}}}}}} <> buf,
              toks} : Lex.Lex}
          lex_ctl5(b0, b1, b2, b3, b4, buf, toks)

# a code point below U+0020, written as \u00XX, reads back as itself
law lex_ctl:
  for +uu: U32
  for h_lt: {U32.is_lt(uu, 32) == True{} : Bool}
  for buf: List<&2, Char>
  for toks: List<&2, Lex.Tok>
  {Lex.run(String.to_list(Print.escape.u(uu)), Lex.Lex{Lex.Str{}, buf, toks}) ==
    Lex.Lex{Lex.Str{}, Chr{uu} <> buf, toks} : Lex.Lex}

def lex_ctl(uu, h_lt, buf, toks):
  match uu:
    case U32{WCon{+b0, WCon{+b1, WCon{+b2, WCon{+b3, WCon{+b4, WCon{+b5, +rest}}}}}}}:
      +c5 = Word.cmp.fin(b5, True{}, Word.cmp(26n, rest, M7.zw(26n)))
      +c4 = Word.cmp.fin(b4, False{}, c5)
      +c3 = Word.cmp.fin(b3, False{}, c4)
      +c2 = Word.cmp.fin(b2, False{}, c3)
      +c1 = Word.cmp.fin(b1, False{}, c2)
      h5 = M7.lt_up(b4, c5, M7.lt_up(b3, c4, M7.lt_up(b2, c3, M7.lt_up(b1, c2, M7.lt_up(b0, c1, h_lt)))))
      lex_ctl.at(Word.cmp(26n, rest, M7.zw(26n)), b5, b0, b1, b2, b3, b4, rest, {==}, h5, buf, toks)

# escape.plain's answer, with each of its tests named, read back
law lex_plain:
  for b34: Bool
  for b92: Bool
  for b8: Bool
  for b12: Bool
  for b10: Bool
  for b13: Bool
  for b9: Bool
  for ct: Bool
  for +uu: U32
  for e34: {U32.is_eq(uu, 34) == b34 : Bool}
  for e92: {U32.is_eq(uu, 92) == b92 : Bool}
  for e8: {U32.is_eq(uu, 8) == b8 : Bool}
  for e12: {U32.is_eq(uu, 12) == b12 : Bool}
  for e10: {U32.is_eq(uu, 10) == b10 : Bool}
  for e13: {U32.is_eq(uu, 13) == b13 : Bool}
  for e9: {U32.is_eq(uu, 9) == b9 : Bool}
  for ect: {U32.is_lt(uu, 32) == ct : Bool}
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {Lex.run(String.to_list(Bool.pick(String, b34, "\\\"", Bool.pick(String, b92, "\\\\", Bool.pick(String, b8, "\\b",
    Bool.pick(String, b12, "\\f", Bool.pick(String, b10, "\\n", Bool.pick(String, b13, "\\r", Bool.pick(String, b9,
    "\\t", Print.escape.rest.go(uu, Chr{uu}, ct))))))))), Lex.Lex{Lex.Str{}, buf, toks}) ==
    Lex.Lex{Lex.Str{}, Chr{uu} <> buf, toks} : Lex.Lex}

def lex_plain(b34, b92, b8, b12, b10, b13, b9, ct, uu, e34, e92, e8, e12, e10, e13, e9, ect, buf, toks):
  match b34:
    case True{}:
      eu = Equal.sym(U32, uu, 34, M7.ueq(uu, 34, e34))
      %eu : {Lex.run(String.to_list("\\\""), Lex.Lex{Lex.Str{}, buf, toks}) == Lex.Lex{Lex.Str{}, Chr{_} <> buf,
        toks} : Lex.Lex}
      {==}
    case False{}:
      match b92:
        case True{}:
          eu = Equal.sym(U32, uu, 92, M7.ueq(uu, 92, e92))
          %eu : {Lex.run(String.to_list("\\\\"), Lex.Lex{Lex.Str{}, buf, toks}) == Lex.Lex{Lex.Str{}, Chr{_} <> buf,
            toks} : Lex.Lex}
          {==}
        case False{}:
          match b8:
            case True{}:
              eu = Equal.sym(U32, uu, 8, M7.ueq(uu, 8, e8))
              %eu : {Lex.run(String.to_list("\\b"), Lex.Lex{Lex.Str{}, buf, toks}) == Lex.Lex{Lex.Str{}, Chr{_} <> buf,
                toks} : Lex.Lex}
              {==}
            case False{}:
              match b12:
                case True{}:
                  eu = Equal.sym(U32, uu, 12, M7.ueq(uu, 12, e12))
                  %eu : {Lex.run(String.to_list("\\f"), Lex.Lex{Lex.Str{}, buf, toks}) == Lex.Lex{Lex.Str{},
                    Chr{_} <> buf, toks} : Lex.Lex}
                  {==}
                case False{}:
                  match b10:
                    case True{}:
                      eu = Equal.sym(U32, uu, 10, M7.ueq(uu, 10, e10))
                      %eu : {Lex.run(String.to_list("\\n"), Lex.Lex{Lex.Str{}, buf, toks}) == Lex.Lex{Lex.Str{},
                        Chr{_} <> buf, toks} : Lex.Lex}
                      {==}
                    case False{}:
                      match b13:
                        case True{}:
                          eu = Equal.sym(U32, uu, 13, M7.ueq(uu, 13, e13))
                          %eu : {Lex.run(String.to_list("\\r"), Lex.Lex{Lex.Str{}, buf, toks}) == Lex.Lex{Lex.Str{},
                            Chr{_} <> buf, toks} : Lex.Lex}
                          {==}
                        case False{}:
                          match b9:
                            case True{}:
                              eu = Equal.sym(U32, uu, 9, M7.ueq(uu, 9, e9))
                              %eu : {Lex.run(String.to_list("\\t"), Lex.Lex{Lex.Str{}, buf,
                                toks}) == Lex.Lex{Lex.Str{}, Chr{_} <> buf, toks} : Lex.Lex}
                              {==}
                            case False{}:
                              match ct:
                                case True{}:
                                  lex_ctl(uu, ect, buf, toks)
                                case False{}:
                                  Equal.trans(Lex.Lex, Lex.feed(Chr{uu}, Lex.Lex{Lex.Str{}, buf, toks}),
                                      Lex.step(Lex.Str{}, Lex.classify(Chr{uu}), Chr{uu}, buf,
                                        toks), Lex.Lex{Lex.Str{}, Chr{uu} <> buf, toks},
                                      M3.feed_as(Chr{uu}, Lex.Str{}, buf, toks, Lex.classify(Chr{uu}), {==}),
                                      M6.str_other(Lex.classify(Chr{uu}), uu, {==}, e34, e92, ect, buf, toks))

# the characters, fixed, reversed onto buf
def fix_rev(cs: List<&2, Char>, buf: List<&2, Char>) -> List<&2, Char>:
  match cs:
    case Nil{}:
      buf
    case Con{hd, tl}:
      fix_rev(tl, M3.fix(hd) <> buf)

# one character's escape, once it is known whether it is a scalar value
law lex_sc:
  for sc: Bool
  for +uu: U32
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {Lex.run(String.to_list(Print.escape.scalar(uu, Chr{uu}, sc)), Lex.Lex{Lex.Str{}, buf, toks}) ==
    Lex.Lex{Lex.Str{}, Bool.pick(Char, sc, Chr{uu}, Chr{65533}) <> buf, toks} : Lex.Lex}

def lex_sc(sc, uu, buf, toks):
  match sc:
    case True{}:
      lex_plain(U32.is_eq(uu, 34), U32.is_eq(uu, 92), U32.is_eq(uu, 8), U32.is_eq(uu, 12), U32.is_eq(uu, 10),
        U32.is_eq(uu, 13), U32.is_eq(uu, 9), U32.is_lt(uu, 32), uu, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
        buf, toks)
    case False{}:
      {==}

# inside a string, a character print escapes reads back fixed
law lex_char:
  for +ch: Char
  for buf: List<&2, Char>
  for toks: List<&2, Lex.Tok>
  {Lex.run(String.to_list(Print.escape.char(ch)), Lex.Lex{Lex.Str{}, buf, toks}) ==
    Lex.Lex{Lex.Str{}, M3.fix(ch) <> buf, toks} : Lex.Lex}

def lex_char(ch, buf, toks):
  match ch:
    case Chr{+uu}:
      lex_sc(Print.scalar(uu), uu, buf, toks)

# inside a string, print's escape of the characters reads back fixed
law lex_esc:
  for +cs: List<&2, Char>
  for +buf: List<&2, Char>
  for +toks: List<&2, Lex.Tok>
  {Lex.run(String.to_list(Print.escape(cs)), Lex.Lex{Lex.Str{}, buf, toks}) ==
    Lex.Lex{Lex.Str{}, fix_rev(cs, buf), toks} : Lex.Lex}

def lex_esc(cs, buf, toks):
  match cs:
    case Nil{}:
      {==}
    case Con{+hd, +tl}:
      Equal.trans(Lex.Lex,
        Lex.run(String.to_list(Print.escape.char(hd) ++ Print.escape(tl)), Lex.Lex{Lex.Str{}, buf, toks}),
        Lex.run(String.to_list(Print.escape(tl)), Lex.Lex{Lex.Str{}, M3.fix(hd) <> buf, toks}),
        Lex.Lex{Lex.Str{}, fix_rev(tl, M3.fix(hd) <> buf), toks},
        Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.escape.char(hd) ++ Print.escape(tl)), Lex.Lex{Lex.Str{}, buf, toks}),
          Lex.run(String.to_list(Print.escape(tl)), Lex.run(String.to_list(Print.escape.char(hd)),
            Lex.Lex{Lex.Str{}, buf, toks})),
          Lex.run(String.to_list(Print.escape(tl)), Lex.Lex{Lex.Str{}, M3.fix(hd) <> buf, toks}),
          M6.run_app(Print.escape.char(hd), Print.escape(tl), Lex.Lex{Lex.Str{}, buf, toks}),
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list(Print.escape(tl)), xx),
            Lex.run(String.to_list(Print.escape.char(hd)), Lex.Lex{Lex.Str{}, buf, toks}),
            Lex.Lex{Lex.Str{}, M3.fix(hd) <> buf, toks}, lex_char(hd, buf, toks))),
        lex_esc(tl, M3.fix(hd) <> buf, toks))

# a buffer of fixed characters, read back
law text_fix:
  for +cs: List<&2, Char>
  for +buf: List<&2, Char>
  for +acc: String
  {Lex.text.go(fix_rev(cs, buf), acc) == Lex.text.go(buf, M3.fixs(cs) ++ acc) : String}

def text_fix(cs, buf, acc):
  match cs:
    case Nil{}:
      {==}
    case Con{+hd, +tl}:
      text_fix(tl, M3.fix(hd) <> buf, acc)

# a quoted string, from between tokens, reads back as one string token of its
# characters, fixed
law lex_quote:
  for +txt: String
  for +toks: List<&2, Lex.Tok>
  {Lex.run(String.to_list(Print.quote(txt)), Lex.Lex{Lex.Idle{}, [], toks}) ==
    Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(txt))} <> toks} : Lex.Lex}

def lex_quote(txt, toks):
  +cs = String.to_list(txt)
  +ee = Print.escape(cs)
  +fr = fix_rev(cs, [])
  Equal.trans(Lex.Lex,
    Lex.run(String.to_list("\"" ++ ee ++ "\""), Lex.Lex{Lex.Idle{}, [], toks}),
    Lex.run(String.to_list("\""), Lex.Lex{Lex.Str{}, fr, toks}),
    Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(cs)} <> toks},
    Equal.trans(Lex.Lex,
      Lex.run(String.to_list("\"" ++ ee ++ "\""), Lex.Lex{Lex.Idle{}, [], toks}),
      Lex.run(String.to_list(ee ++ "\""), Lex.Lex{Lex.Str{}, [], toks}),
      Lex.run(String.to_list("\""), Lex.Lex{Lex.Str{}, fr, toks}),
      M6.run_app("\"", ee ++ "\"", Lex.Lex{Lex.Idle{}, [], toks}),
      Equal.trans(Lex.Lex,
        Lex.run(String.to_list(ee ++ "\""), Lex.Lex{Lex.Str{}, [], toks}),
        Lex.run(String.to_list("\""), Lex.run(String.to_list(ee), Lex.Lex{Lex.Str{}, [], toks})),
        Lex.run(String.to_list("\""), Lex.Lex{Lex.Str{}, fr, toks}),
        M6.run_app(ee, "\"", Lex.Lex{Lex.Str{}, [], toks}),
        Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("\""), xx), Lex.run(String.to_list(ee),
          Lex.Lex{Lex.Str{}, [], toks}),
          Lex.Lex{Lex.Str{}, fr, toks}, lex_esc(cs, [], toks)))),
    Equal.cong(String, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TStr{xx} <> toks}, Lex.text(fr), M3.fixs(cs),
      Equal.trans(String, Lex.text.go(fr, ""), M3.fixs(cs) ++ "", M3.fixs(cs), text_fix(cs, [], ""),
        M3.append_nil(M3.fixs(cs)))))

# what lexp says of a value by its shape: a value's text leads to pend; an
# array's or object's cells, then the closing bracket, push their tokens
def lg(+val: V.Json, sh: V.Shape, +acc: List<&2, Lex.Tok>) -> Type:
  match sh:
    case V.WVal{}:
      {Lex.run(String.to_list(Print.print(val)), Lex.Lex{Lex.Idle{}, [], acc}) == M4.pend(val, acc) : Lex.Lex}
    case V.WArr{}:
      {Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(val)), Lex.Lex{Lex.Idle{}, [], acc})) ==
        Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(val, V.WArr{}), acc)} : Lex.Lex}
    case V.WObj{}:
      {Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(val)), Lex.Lex{Lex.Idle{}, [], acc})) ==
        Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(val, V.WObj{}), acc)} : Lex.Lex}

# lexp for a boolean
law lexp_bool:
  for bb: Bool
  for +acc: List<&2, Lex.Tok>
  lg(V.JBool{bb}, V.WVal{}, acc)

def lexp_bool(bb, _acc):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# lexp for an array cell, by what follows it
law lexp_cons:
  for tl: V.Json
  for +hd: V.Json
  for +h: {V.wf.go(V.JCons{hd, tl}, V.WArr{}) == True{} : Bool}
  for +acc: List<&2, Lex.Tok>
  for ih_hd: {V.wf.go(hd, V.WVal{}) == True{} : Bool} -> lg(hd, V.WVal{}, acc)
  for ih_tl: {V.wf.go(tl, V.WArr{}) == True{} : Bool} -> lg(tl, V.WArr{}, Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
    M3.tj(hd, V.WVal{}), acc))
  lg(V.JCons{hd, tl}, V.WArr{}, acc)

def lexp_cons(tl, hd, h, acc, ih_hd, ih_tl):
  match tl:
    case V.JNil{}:
      hd_ok = M3.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNil{}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(hd)), Lex.Lex{Lex.Idle{},
        [], acc})), Lex.run(String.to_list("]"), M4.pend(hd, acc)), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)}, Equal.cong(Lex.Lex, Lex.Lex,
          xx => Lex.run(String.to_list("]"), xx), Lex.run(String.to_list(Print.print(hd)), Lex.Lex{Lex.Idle{}, [],
          acc}), M4.pend(hd, acc), ih_hd(hd_ok)), M4.close(hd, ']', Lex.TCloseArr{}, {==}, acc))
    case V.JNull{}:
      hd_ok = M3.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNull{}, V.WArr{}), h)
      tl_ok = M3.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNull{}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JNull{}))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JNull{}}, V.WArr{}), acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JNull{}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JNull{}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JNull{})), M4.pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), M6.seq(Print.print(hd), "," ++ Print.print(V.JNull{}),
              Lex.Lex{Lex.Idle{},
          [], acc}, M4.pend(hd, acc), ih_hd(hd_ok)), M6.seq(",", Print.print(V.JNull{}), M4.pend(hd, acc),
              Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)}, M4.close(hd, ',', Lex.TComma{},
              {==},
          acc)))), Equal.trans(Lex.Lex, Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JNull{})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JNull{}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JNull{}}, V.WArr{}), acc)}, ih_tl(tl_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd,
          V.JNull{}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          M3.tj(V.JNull{}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JNull{},
          V.WArr{})), acc), List.reverse.go(&2, Lex.Tok, M3.tj(V.JNull{}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)), M7.rev_app(M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JNull{},
              V.WArr{}), acc)))))
    case V.JBool{+t1}:
      hd_ok = M3.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JBool{t1}, V.WArr{}), h)
      tl_ok = M3.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JBool{t1}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JBool{t1}))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JBool{t1}}, V.WArr{}), acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JBool{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JBool{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JBool{t1})), M4.pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), M6.seq(Print.print(hd), "," ++ Print.print(V.JBool{t1}),
              Lex.Lex{Lex.Idle{},
          [], acc}, M4.pend(hd, acc), ih_hd(hd_ok)), M6.seq(",", Print.print(V.JBool{t1}), M4.pend(hd, acc),
              Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)}, M4.close(hd, ',', Lex.TComma{},
              {==},
          acc)))), Equal.trans(Lex.Lex, Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JBool{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JBool{t1}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JBool{t1}}, V.WArr{}), acc)},
              ih_tl(tl_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd,
          V.JBool{t1}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          M3.tj(V.JBool{t1}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JBool{t1},
          V.WArr{})), acc), List.reverse.go(&2, Lex.Tok, M3.tj(V.JBool{t1}, V.WArr{}),
              Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)), M7.rev_app(M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JBool{t1},
              V.WArr{}),
          acc)))))
    case V.JNum{+t1}:
      hd_ok = M3.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNum{t1}, V.WArr{}), h)
      tl_ok = M3.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JNum{t1}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JNum{t1}))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JNum{t1}}, V.WArr{}), acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JNum{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JNum{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JNum{t1})), M4.pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), M6.seq(Print.print(hd), "," ++ Print.print(V.JNum{t1}),
              Lex.Lex{Lex.Idle{},
          [], acc}, M4.pend(hd, acc), ih_hd(hd_ok)), M6.seq(",", Print.print(V.JNum{t1}), M4.pend(hd, acc),
              Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)}, M4.close(hd, ',', Lex.TComma{},
              {==},
          acc)))), Equal.trans(Lex.Lex, Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JNum{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JNum{t1}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JNum{t1}}, V.WArr{}), acc)}, ih_tl(tl_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd,
          V.JNum{t1}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          M3.tj(V.JNum{t1}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JNum{t1},
          V.WArr{})), acc), List.reverse.go(&2, Lex.Tok, M3.tj(V.JNum{t1}, V.WArr{}),
              Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)), M7.rev_app(M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JNum{t1},
              V.WArr{}), acc)))))
    case V.JStr{+t1}:
      hd_ok = M3.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JStr{t1}, V.WArr{}), h)
      tl_ok = M3.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JStr{t1}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JStr{t1}))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JStr{t1}}, V.WArr{}), acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JStr{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JStr{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JStr{t1})), M4.pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), M6.seq(Print.print(hd), "," ++ Print.print(V.JStr{t1}),
              Lex.Lex{Lex.Idle{},
          [], acc}, M4.pend(hd, acc), ih_hd(hd_ok)), M6.seq(",", Print.print(V.JStr{t1}), M4.pend(hd, acc),
              Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)}, M4.close(hd, ',', Lex.TComma{},
              {==},
          acc)))), Equal.trans(Lex.Lex, Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JStr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JStr{t1}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JStr{t1}}, V.WArr{}), acc)}, ih_tl(tl_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd,
          V.JStr{t1}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          M3.tj(V.JStr{t1}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JStr{t1},
          V.WArr{})), acc), List.reverse.go(&2, Lex.Tok, M3.tj(V.JStr{t1}, V.WArr{}),
              Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)), M7.rev_app(M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JStr{t1},
              V.WArr{}), acc)))))
    case V.JArr{+t1}:
      hd_ok = M3.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JArr{t1}, V.WArr{}), h)
      tl_ok = M3.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JArr{t1}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JArr{t1}))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JArr{t1}}, V.WArr{}), acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JArr{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JArr{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JArr{t1})), M4.pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), M6.seq(Print.print(hd), "," ++ Print.print(V.JArr{t1}),
              Lex.Lex{Lex.Idle{},
          [], acc}, M4.pend(hd, acc), ih_hd(hd_ok)), M6.seq(",", Print.print(V.JArr{t1}), M4.pend(hd, acc),
              Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)}, M4.close(hd, ',', Lex.TComma{},
              {==},
          acc)))), Equal.trans(Lex.Lex, Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JArr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JArr{t1}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JArr{t1}}, V.WArr{}), acc)}, ih_tl(tl_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd,
          V.JArr{t1}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          M3.tj(V.JArr{t1}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JArr{t1},
          V.WArr{})), acc), List.reverse.go(&2, Lex.Tok, M3.tj(V.JArr{t1}, V.WArr{}),
              Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)), M7.rev_app(M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JArr{t1},
              V.WArr{}), acc)))))
    case V.JObj{+t1}:
      hd_ok = M3.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JObj{t1}, V.WArr{}), h)
      tl_ok = M3.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JObj{t1}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JObj{t1}))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JObj{t1}}, V.WArr{}), acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JObj{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JObj{t1}))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JObj{t1})), M4.pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), M6.seq(Print.print(hd), "," ++ Print.print(V.JObj{t1}),
              Lex.Lex{Lex.Idle{},
          [], acc}, M4.pend(hd, acc), ih_hd(hd_ok)), M6.seq(",", Print.print(V.JObj{t1}), M4.pend(hd, acc),
              Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)}, M4.close(hd, ',', Lex.TComma{},
              {==},
          acc)))), Equal.trans(Lex.Lex, Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JObj{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JObj{t1}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JObj{t1}}, V.WArr{}), acc)}, ih_tl(tl_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd,
          V.JObj{t1}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          M3.tj(V.JObj{t1}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JObj{t1},
          V.WArr{})), acc), List.reverse.go(&2, Lex.Tok, M3.tj(V.JObj{t1}, V.WArr{}),
              Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)), M7.rev_app(M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JObj{t1},
              V.WArr{}), acc)))))
    case V.JCons{+t1, +t2}:
      hd_ok = M3.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JCons{t1, t2}, V.WArr{}), h)
      tl_ok = M3.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JCons{t1, t2}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JCons{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JCons{t1,
        t2})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JCons{t1, t2}},
          V.WArr{}), acc)}, Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JCons{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JCons{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list("," ++ Print.print(V.JCons{t1, t2})), M4.pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), M6.seq(Print.print(hd),
          "," ++ Print.print(V.JCons{t1, t2}), Lex.Lex{Lex.Idle{}, [], acc}, M4.pend(hd, acc), ih_hd(hd_ok)),
              M6.seq(",",
          Print.print(V.JCons{t1, t2}), M4.pend(hd, acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)}, M4.close(hd, ',', Lex.TComma{}, {==}, acc)))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{t1, t2}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JCons{t1, t2}}, V.WArr{}), acc)},
          ih_tl(tl_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          M3.tj(V.JCons{hd, V.JCons{t1, t2}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{t1, t2}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))}, Equal.cong(List<&2, Lex.Tok>,
              Lex.Lex,
          xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx}, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
          M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JCons{t1, t2}, V.WArr{})), acc), List.reverse.go(&2, Lex.Tok,
          M3.tj(V.JCons{t1, t2}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)),
          M7.rev_app(M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JCons{t1, t2}, V.WArr{}), acc)))))
    case V.JPair{+t1, +t2, +t3}:
      hd_ok = M3.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JPair{t1, t2, t3}, V.WArr{}), h)
      tl_ok = M3.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JPair{t1, t2, t3}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JPair{t1, t2,
        t3})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JPair{t1, t2,
              t3}},
          V.WArr{}), acc)}, Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list("," ++ Print.print(V.JPair{t1, t2, t3})), M4.pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), M6.seq(Print.print(hd),
          "," ++ Print.print(V.JPair{t1, t2, t3}), Lex.Lex{Lex.Idle{}, [], acc}, M4.pend(hd, acc), ih_hd(hd_ok)),
              M6.seq(",",
          Print.print(V.JPair{t1, t2, t3}), M4.pend(hd, acc), Lex.Lex{Lex.Idle{}, [],
              Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)}, M4.close(hd, ',', Lex.TComma{}, {==}, acc)))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JPair{t1, t2, t3}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JPair{t1, t2, t3}}, V.WArr{}), acc)},
          ih_tl(tl_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          M3.tj(V.JCons{hd, V.JPair{t1, t2, t3}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JPair{t1, t2, t3}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))}, Equal.cong(List<&2, Lex.Tok>,
              Lex.Lex,
          xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx}, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
          M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JPair{t1, t2, t3}, V.WArr{})), acc), List.reverse.go(&2, Lex.Tok,
          M3.tj(V.JPair{t1, t2, t3}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)),
          M7.rev_app(M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JPair{t1, t2, t3}, V.WArr{}), acc)))))
    case V.JSpan{+t1, +t2}:
      hd_ok = M3.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JSpan{t1, t2}, V.WArr{}), h)
      tl_ok = M3.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JSpan{t1, t2}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JSpan{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JSpan{t1,
        t2})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JSpan{t1, t2}},
          V.WArr{}), acc)}, Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JSpan{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JSpan{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list("," ++ Print.print(V.JSpan{t1, t2})), M4.pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), M6.seq(Print.print(hd),
          "," ++ Print.print(V.JSpan{t1, t2}), Lex.Lex{Lex.Idle{}, [], acc}, M4.pend(hd, acc), ih_hd(hd_ok)),
              M6.seq(",",
          Print.print(V.JSpan{t1, t2}), M4.pend(hd, acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(hd, V.WVal{}), acc)}, M4.close(hd, ',', Lex.TComma{}, {==}, acc)))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JSpan{t1, t2}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JSpan{t1, t2}}, V.WArr{}), acc)},
          ih_tl(tl_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          M3.tj(V.JCons{hd, V.JSpan{t1, t2}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JSpan{t1, t2}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))}, Equal.cong(List<&2, Lex.Tok>,
              Lex.Lex,
          xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx}, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
          M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JSpan{t1, t2}, V.WArr{})), acc), List.reverse.go(&2, Lex.Tok,
          M3.tj(V.JSpan{t1, t2}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)),
          M7.rev_app(M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JSpan{t1, t2}, V.WArr{}), acc)))))
    case V.JBind{+t1, +t2, +t3, +t4}:
      hd_ok = M3.stop_l(V.wf.go(hd, V.WVal{}), V.wf.go(V.JBind{t1, t2, t3, t4}, V.WArr{}), h)
      tl_ok = M3.stop_r(V.wf.go(hd, V.WVal{}), V.wf.go(V.JBind{t1, t2, t3, t4}, V.WArr{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
        Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))), Lex.Lex{Lex.Idle{},
        [], acc})), Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3,
        t4})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JBind{t1, t2, t3,
          t4}}, V.WArr{}), acc)}, Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("]"), xx),
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))), Lex.Lex{Lex.Idle{},
          [], acc}), Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(hd) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))), Lex.Lex{Lex.Idle{},
          [], acc}), Lex.run(String.to_list("," ++ Print.print(V.JBind{t1, t2, t3, t4})), M4.pend(hd, acc)),
          Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)}), M6.seq(Print.print(hd),
          "," ++ Print.print(V.JBind{t1, t2, t3, t4}), Lex.Lex{Lex.Idle{}, [], acc}, M4.pend(hd, acc), ih_hd(hd_ok)),
          M6.seq(",", Print.print(V.JBind{t1, t2, t3, t4}), M4.pend(hd, acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)}, M4.close(hd, ',', Lex.TComma{}, {==},
          acc)))), Equal.trans(Lex.Lex, Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(V.JBind{t1, t2,
          t3, t4})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JBind{t1, t2, t3, t4},
          V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{hd, V.JBind{t1, t2, t3, t4}}, V.WArr{}), acc)},
          ih_tl(tl_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok,
          M3.tj(V.JCons{hd, V.JBind{t1, t2, t3, t4}}, V.WArr{}), acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JBind{t1, t2, t3, t4}, V.WArr{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc))}, Equal.cong(List<&2, Lex.Tok>,
              Lex.Lex,
          xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> xx}, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
          M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JBind{t1, t2, t3, t4}, V.WArr{})), acc), List.reverse.go(&2,
              Lex.Tok,
          M3.tj(V.JBind{t1, t2, t3, t4}, V.WArr{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}),
              acc)),
          M7.rev_app(M3.tj(hd, V.WVal{}), Lex.TComma{} <> M3.tj(V.JBind{t1, t2, t3, t4}, V.WArr{}), acc)))))

# lexp for an object cell, by what follows it
law lexp_pair:
  for rr: V.Json
  for +kk: String
  for +vv: V.Json
  for +h: {V.wf.go(V.JPair{kk, vv, rr}, V.WObj{}) == True{} : Bool}
  for +acc: List<&2, Lex.Tok>
  for ih_v: {V.wf.go(vv, V.WVal{}) == True{} : Bool} -> lg(vv, V.WVal{},
    Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)
  for ih_r: {V.wf.go(rr, V.WObj{}) == True{} : Bool} -> lg(rr, V.WObj{}, Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
    M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))
  lg(V.JPair{kk, vv, rr}, V.WObj{}, acc)

def lexp_pair(rr, kk, vv, h, acc, ih_v, ih_r):
  match rr:
    case V.JNil{}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNil{}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ Print.print(vv))), Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("}"), M4.pend(vv, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, Equal.cong(Lex.Lex, Lex.Lex,
          xx => Lex.run(String.to_list("}"), xx), Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ Print.print(vv))),
          Lex.Lex{Lex.Idle{}, [], acc}), M4.pend(vv, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ Print.print(vv))), Lex.Lex{Lex.Idle{},
          [], acc}), Lex.run(String.to_list(":" ++ Print.print(vv)), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), M6.seq(Print.quote(kk), ":" ++ Print.print(vv),
          Lex.Lex{Lex.Idle{}, [], acc}, Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc},
          lex_quote(kk, acc)), Equal.trans(Lex.Lex, Lex.run(String.to_list(":" ++ Print.print(vv)), Lex.Lex{Lex.Idle{},
          [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(vv)),
              Lex.Lex{Lex.Idle{},
          [], Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), M6.seq(":", Print.print(vv),
              Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, {==}), ih_v(v_ok)))), M4.close(vv, '}',
          Lex.TCloseObj{}, {==}, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))
    case V.JNull{}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))))),
        Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JNull{}, V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JNull{})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)),
              Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
              Lex.run(String.to_list(Print.print(V.JNull{})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JNull{})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)),
              Lex.run(String.to_list(Print.print(V.JNull{})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(Print.print(vv),
          "," ++ Print.print(V.JNull{}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), M6.seq(",",
              Print.print(V.JNull{}),
          M4.pend(vv, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, M4.close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JNull{}, V.WObj{}),
              Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))},
              Lex.Lex{Lex.Idle{},
          [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JNull{}, V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)},
          ih_r(r_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JNull{}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JNull{}, V.WObj{}),
              Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))},
              Equal.cong(List<&2,
          Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JNull{}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, M3.tj(V.JNull{},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)), M7.rev_app(M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JNull{}, V.WObj{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))
    case V.JBool{+t1}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBool{t1}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBool{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))))),
        Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JBool{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1})))), Lex.Lex{Lex.Idle{},
          [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JBool{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)),
              Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1})))), Lex.Lex{Lex.Idle{},
          [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JBool{t1})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}),
              M6.seq(Print.print(vv),
          "," ++ Print.print(V.JBool{t1}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), M6.seq(",",
              Print.print(V.JBool{t1}),
          M4.pend(vv, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, M4.close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JBool{t1}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JBool{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)},
          ih_r(r_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JBool{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JBool{t1}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
          xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
          M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JBool{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, M3.tj(V.JBool{t1},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)), M7.rev_app(M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JBool{t1}, V.WObj{}),
              Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))
    case V.JNum{+t1}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNum{t1}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNum{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))))),
        Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JNum{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JNum{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)),
              Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
              Lex.run(String.to_list(Print.print(V.JNum{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JNum{t1})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)),
              Lex.run(String.to_list(Print.print(V.JNum{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(Print.print(vv),
          "," ++ Print.print(V.JNum{t1}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), M6.seq(",",
              Print.print(V.JNum{t1}),
          M4.pend(vv, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, M4.close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JNum{t1}, V.WObj{}),
              Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))},
              Lex.Lex{Lex.Idle{},
          [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JNum{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)},
          ih_r(r_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JNum{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JNum{t1}, V.WObj{}),
              Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))},
              Equal.cong(List<&2,
          Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JNum{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, M3.tj(V.JNum{t1},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)), M7.rev_app(M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JNum{t1}, V.WObj{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))
    case V.JStr{+t1}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JStr{t1}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JStr{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))))),
        Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JStr{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JStr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)),
              Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
              Lex.run(String.to_list(Print.print(V.JStr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JStr{t1})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)),
              Lex.run(String.to_list(Print.print(V.JStr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(Print.print(vv),
          "," ++ Print.print(V.JStr{t1}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), M6.seq(",",
              Print.print(V.JStr{t1}),
          M4.pend(vv, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, M4.close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JStr{t1}, V.WObj{}),
              Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))},
              Lex.Lex{Lex.Idle{},
          [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JStr{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)},
          ih_r(r_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JStr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JStr{t1}, V.WObj{}),
              Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))},
              Equal.cong(List<&2,
          Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JStr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, M3.tj(V.JStr{t1},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)), M7.rev_app(M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JStr{t1}, V.WObj{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))
    case V.JArr{+t1}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JArr{t1}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JArr{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))))),
        Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JArr{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JArr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)),
              Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
              Lex.run(String.to_list(Print.print(V.JArr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JArr{t1})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)),
              Lex.run(String.to_list(Print.print(V.JArr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(Print.print(vv),
          "," ++ Print.print(V.JArr{t1}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), M6.seq(",",
              Print.print(V.JArr{t1}),
          M4.pend(vv, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, M4.close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JArr{t1}, V.WObj{}),
              Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))},
              Lex.Lex{Lex.Idle{},
          [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JArr{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)},
          ih_r(r_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JArr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JArr{t1}, V.WObj{}),
              Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))},
              Equal.cong(List<&2,
          Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JArr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, M3.tj(V.JArr{t1},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)), M7.rev_app(M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JArr{t1}, V.WObj{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))
    case V.JObj{+t1}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JObj{t1}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JObj{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))))),
        Lex.Lex{Lex.Idle{}, [],
        acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JObj{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JObj{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)),
              Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
              Lex.run(String.to_list(Print.print(V.JObj{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JObj{t1})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)),
              Lex.run(String.to_list(Print.print(V.JObj{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(Print.print(vv),
          "," ++ Print.print(V.JObj{t1}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), M6.seq(",",
              Print.print(V.JObj{t1}),
          M4.pend(vv, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, M4.close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JObj{t1}, V.WObj{}),
              Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))},
              Lex.Lex{Lex.Idle{},
          [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JObj{t1}, V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)},
          ih_r(r_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JObj{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JObj{t1}, V.WObj{}),
              Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))},
              Equal.cong(List<&2,
          Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JObj{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, M3.tj(V.JObj{t1},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)), M7.rev_app(M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JObj{t1}, V.WObj{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))
    case V.JCons{+t1, +t2}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JCons{t1, t2}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JCons{t1, t2}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))))),
        Lex.Lex{Lex.Idle{}, [], acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JCons{t1,
        t2})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JCons{t1, t2}, V.WObj{})),
              Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1,
          t2}))))), Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JCons{t1, t2})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1,
          t2}))))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)),
              Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JCons{t1,
          t2})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JCons{t1, t2})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)), Lex.run(String.to_list(Print.print(V.JCons{t1,
          t2})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(Print.print(vv),
          "," ++ Print.print(V.JCons{t1, t2}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), M6.seq(",",
              Print.print(V.JCons{t1,
          t2}), M4.pend(vv, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, M4.close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{t1, t2}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JCons{t1, t2}, V.WObj{})),
              Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)},
          ih_r(r_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JCons{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{t1, t2}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
          xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
          M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JCons{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{t1,
              t2},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)), M7.rev_app(M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JCons{t1, t2}, V.WObj{}),
              Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))
    case V.JPair{+t1, +t2, +t3}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{t1, t2, t3}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{t1, t2, t3}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2,
        t3}))))), Lex.Lex{Lex.Idle{}, [], acc})), Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JPair{t1, t2, t3}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, Equal.cong(Lex.Lex, Lex.Lex,
          xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2,
          t3}))))), Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2,
          t3}))))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)),
              Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JPair{t1,
          t2, t3})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JPair{t1, t2, t3})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)), Lex.run(String.to_list(Print.print(V.JPair{t1,
          t2, t3})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(Print.print(vv),
          "," ++ Print.print(V.JPair{t1, t2, t3}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), M6.seq(",",
              Print.print(V.JPair{t1, t2,
          t3}), M4.pend(vv, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, M4.close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JPair{t1, t2, t3}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JPair{t1, t2, t3}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, ih_r(r_ok), Equal.sym(Lex.Lex,
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JPair{t1, t2, t3}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JPair{t1, t2, t3}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
          xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
          M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JPair{t1, t2, t3}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, M3.tj(V.JPair{t1,
              t2,
          t3}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)), M7.rev_app(M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JPair{t1, t2, t3}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))
    case V.JSpan{+t1, +t2}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JSpan{t1, t2}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JSpan{t1, t2}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))))),
        Lex.Lex{Lex.Idle{}, [], acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JSpan{t1,
        t2})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JSpan{t1, t2}, V.WObj{})),
              Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1,
          t2}))))), Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1,
          t2}))))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)),
              Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}), Lex.run(String.to_list(Print.print(V.JSpan{t1,
          t2})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JSpan{t1, t2})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)), Lex.run(String.to_list(Print.print(V.JSpan{t1,
          t2})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(Print.print(vv),
          "," ++ Print.print(V.JSpan{t1, t2}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), M6.seq(",",
              Print.print(V.JSpan{t1,
          t2}), M4.pend(vv, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, M4.close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JSpan{t1, t2}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JSpan{t1, t2}, V.WObj{})),
              Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)},
          ih_r(r_ok), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JSpan{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JSpan{t1, t2}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
          xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
          M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JSpan{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, M3.tj(V.JSpan{t1,
              t2},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)), M7.rev_app(M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JSpan{t1, t2}, V.WObj{}),
              Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))
    case V.JBind{+t1, +t2, +t3, +t4}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{t1, t2, t3, t4}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{t1, t2, t3, t4}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
        Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3,
        t4}))))), Lex.Lex{Lex.Idle{}, [], acc})), Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JBind{t1, t2, t3, t4}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, Equal.cong(Lex.Lex, Lex.Lex,
          xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3,
          t4}))))), Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.quote(kk) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3,
          t4}))))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(Print.quote(kk),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, lex_quote(kk, acc)),
              Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))), Lex.Lex{Lex.Idle{},
          [], Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))), Lex.Lex{Lex.Idle{},
          [], Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JBind{t1, t2, t3, t4})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)), Lex.run(String.to_list(Print.print(V.JBind{t1,
          t2, t3, t4})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}), M6.seq(Print.print(vv),
          "," ++ Print.print(V.JBind{t1, t2, t3, t4}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), ih_v(v_ok)), M6.seq(",",
              Print.print(V.JBind{t1, t2,
          t3, t4}), M4.pend(vv, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, M4.close(vv, ',', Lex.TComma{}, {==},
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))), Equal.trans(Lex.Lex,
          Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)})), Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JBind{t1, t2, t3, t4}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JBind{t1, t2, t3, t4}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, ih_r(r_ok), Equal.sym(Lex.Lex,
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JBind{t1, t2, t3, t4}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)}, Lex.Lex{Lex.Idle{}, [],
          Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JBind{t1, t2, t3, t4}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc))}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex,
          xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx}, List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
          M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JBind{t1, t2, t3, t4}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), List.reverse.go(&2, Lex.Tok, M3.tj(V.JBind{t1,
              t2,
          t3, t4}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)), M7.rev_app(M3.tj(vv, V.WVal{}),
          Lex.TComma{} <> M3.tj(V.JBind{t1, t2, t3, t4}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))))

# lexp for an object cell with a span key, by what follows it
law lexp_bind:
  for rr: V.Json
  for +src: String
  for +nn: U32
  for +vv: V.Json
  for +h: {V.wf.go(V.JBind{src, nn, vv, rr}, V.WObj{}) == True{} : Bool}
  for +acc: List<&2, Lex.Tok>
  for ih_v: {V.wf.go(vv, V.WVal{}) == True{} : Bool} -> lg(vv, V.WVal{},
    Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)
  for ih_r: {V.wf.go(rr, V.WObj{}) == True{} : Bool} -> lg(rr, V.WObj{}, Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
    M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
        U32.is_zero(nn))))} <> acc))
  lg(V.JBind{src, nn, vv, rr}, V.WObj{}, acc)

def lexp_bind(rr, src, nn, vv, h, acc, ih_v, ih_r):
  match rr:
    case V.JNil{}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNil{}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ Print.print(vv))), Lex.Lex{Lex.Idle{}, [], acc})), Lex.run(String.to_list("}"),
          M4.pend(vv, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn, U32.is_zero(nn))) ++ (":" ++ Print.print(vv))),
          Lex.Lex{Lex.Idle{}, [], acc}), M4.pend(vv, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc), Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ Print.print(vv))), Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ Print.print(vv)), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          M6.seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))), ":" ++ Print.print(vv), Lex.Lex{Lex.Idle{}, [],
              acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ Print.print(vv)), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv)), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), M6.seq(":",
          Print.print(vv), Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, {==}),
          ih_v(v_ok)))), M4.close(vv, '}', Lex.TCloseObj{}, {==},
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))
    case V.JNull{}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNull{}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))))), Lex.Lex{Lex.Idle{}, [],
          acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JNull{}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), M6.seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNull{})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), M6.seq(":", Print.print(vv) ++ ("," ++ Print.print(V.JNull{})),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNull{}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JNull{})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), M6.seq(Print.print(vv), "," ++ Print.print(V.JNull{}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          M6.seq(",", Print.print(V.JNull{}), M4.pend(vv,
              Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          M4.close(vv, ',', Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JNull{})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)})), Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          M3.tj(V.JNull{}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JNull{}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JNull{}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JNull{}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JNull{},
          V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          List.reverse.go(&2, Lex.Tok, M3.tj(V.JNull{}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
              M3.tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          M7.rev_app(M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JNull{}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))
    case V.JBool{+t1}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBool{t1}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBool{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JBool{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))))), Lex.Lex{Lex.Idle{},
          [], acc}), Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))))), Lex.Lex{Lex.Idle{},
          [], acc}), Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), M6.seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1})))), Lex.Lex{Lex.Idle{},
          [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), M6.seq(":", Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBool{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JBool{t1})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), M6.seq(Print.print(vv), "," ++ Print.print(V.JBool{t1}), Lex.Lex{Lex.Idle{},
              [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          M6.seq(",", Print.print(V.JBool{t1}), M4.pend(vv,
              Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          M4.close(vv, ',', Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JBool{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)})), Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          M3.tj(V.JBool{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JBool{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JBool{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JBool{t1}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JBool{t1},
          V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          List.reverse.go(&2, Lex.Tok, M3.tj(V.JBool{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
              M3.tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          M7.rev_app(M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JBool{t1}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))
    case V.JNum{+t1}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNum{t1}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JNum{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JNum{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), M6.seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), M6.seq(":", Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JNum{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JNum{t1})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), M6.seq(Print.print(vv), "," ++ Print.print(V.JNum{t1}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          M6.seq(",", Print.print(V.JNum{t1}), M4.pend(vv,
              Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          M4.close(vv, ',', Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JNum{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)})), Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          M3.tj(V.JNum{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JNum{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JNum{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JNum{t1}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JNum{t1},
          V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          List.reverse.go(&2, Lex.Tok, M3.tj(V.JNum{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
              M3.tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          M7.rev_app(M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JNum{t1}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))
    case V.JStr{+t1}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JStr{t1}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JStr{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JStr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), M6.seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), M6.seq(":", Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JStr{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JStr{t1})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), M6.seq(Print.print(vv), "," ++ Print.print(V.JStr{t1}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          M6.seq(",", Print.print(V.JStr{t1}), M4.pend(vv,
              Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          M4.close(vv, ',', Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JStr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)})), Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          M3.tj(V.JStr{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JStr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JStr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JStr{t1}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JStr{t1},
          V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          List.reverse.go(&2, Lex.Tok, M3.tj(V.JStr{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
              M3.tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          M7.rev_app(M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JStr{t1}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))
    case V.JArr{+t1}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JArr{t1}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JArr{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JArr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), M6.seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), M6.seq(":", Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JArr{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JArr{t1})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), M6.seq(Print.print(vv), "," ++ Print.print(V.JArr{t1}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          M6.seq(",", Print.print(V.JArr{t1}), M4.pend(vv,
              Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          M4.close(vv, ',', Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JArr{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)})), Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          M3.tj(V.JArr{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JArr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JArr{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JArr{t1}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JArr{t1},
          V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          List.reverse.go(&2, Lex.Tok, M3.tj(V.JArr{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
              M3.tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          M7.rev_app(M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JArr{t1}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))
    case V.JObj{+t1}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JObj{t1}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JObj{t1}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc})), Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JObj{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))))), Lex.Lex{Lex.Idle{}, [],
          acc}), Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), M6.seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1})))), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), M6.seq(":", Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1})),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}, {==}), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JObj{t1}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list("," ++ Print.print(V.JObj{t1})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)}), M6.seq(Print.print(vv), "," ++ Print.print(V.JObj{t1}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          M6.seq(",", Print.print(V.JObj{t1}), M4.pend(vv,
              Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          M4.close(vv, ',', Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JObj{t1})), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)})), Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok,
          M3.tj(V.JObj{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JObj{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JObj{t1}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JObj{t1}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JObj{t1},
          V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          List.reverse.go(&2, Lex.Tok, M3.tj(V.JObj{t1}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
              M3.tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          M7.rev_app(M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JObj{t1}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))
    case V.JCons{+t1, +t2}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JCons{t1, t2}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JCons{t1, t2}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1,
        t2}))))), Lex.Lex{Lex.Idle{}, [], acc})), Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JCons{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          M6.seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}), M6.seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, {==}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JCons{t1, t2}))),
          Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}), Lex.run(String.to_list("," ++ Print.print(V.JCons{t1, t2})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          M6.seq(Print.print(vv), "," ++ Print.print(V.JCons{t1, t2}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          M6.seq(",", Print.print(V.JCons{t1, t2}), M4.pend(vv,
              Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src,
          nn, U32.is_zero(nn))))} <> acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
              M3.tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          M4.close(vv, ',', Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JCons{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{t1, t2}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JCons{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JCons{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{t1, t2}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JCons{t1,
              t2},
          V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{t1, t2}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
          M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)), M7.rev_app(M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JCons{t1, t2},
              V.WObj{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))
    case V.JPair{+t1, +t2, +t3}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{t1, t2, t3}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JPair{t1, t2, t3}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2,
        t3}))))), Lex.Lex{Lex.Idle{}, [], acc})), Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JPair{t1, t2, t3}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{},
          [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          M6.seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}), M6.seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, {==}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JPair{t1, t2, t3}))),
          Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}), Lex.run(String.to_list("," ++ Print.print(V.JPair{t1, t2, t3})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          M6.seq(Print.print(vv), "," ++ Print.print(V.JPair{t1, t2, t3}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          M6.seq(",", Print.print(V.JPair{t1, t2, t3}), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
              M4.close(vv, ',',
          Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JPair{t1, t2, t3})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JPair{t1, t2, t3}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JPair{t1, t2, t3}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JPair{t1, t2, t3}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JPair{t1, t2, t3}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JPair{t1,
              t2,
          t3}, V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc), List.reverse.go(&2, Lex.Tok, M3.tj(V.JPair{t1, t2, t3}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
              M7.rev_app(M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JPair{t1, t2, t3}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))
    case V.JSpan{+t1, +t2}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JSpan{t1, t2}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JSpan{t1, t2}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1,
        t2}))))), Lex.Lex{Lex.Idle{}, [], acc})), Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JSpan{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          M6.seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}), M6.seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, {==}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JSpan{t1, t2}))),
          Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}), Lex.run(String.to_list("," ++ Print.print(V.JSpan{t1, t2})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          M6.seq(Print.print(vv), "," ++ Print.print(V.JSpan{t1, t2}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          M6.seq(",", Print.print(V.JSpan{t1, t2}), M4.pend(vv,
              Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src,
          nn, U32.is_zero(nn))))} <> acc), Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
              M3.tj(vv,
          V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          M4.close(vv, ',', Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JSpan{t1, t2})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JSpan{t1, t2}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JSpan{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JSpan{t1, t2}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JSpan{t1, t2}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JSpan{t1,
              t2},
          V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          List.reverse.go(&2, Lex.Tok, M3.tj(V.JSpan{t1, t2}, V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
          M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)), M7.rev_app(M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JSpan{t1, t2},
              V.WObj{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))
    case V.JBind{+t1, +t2, +t3, +t4}:
      v_ok = M3.stop_l(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{t1, t2, t3, t4}, V.WObj{}), h)
      r_ok = M3.stop_r(V.wf.go(vv, V.WVal{}), V.wf.go(V.JBind{t1, t2, t3, t4}, V.WObj{}), h)
      Equal.trans(Lex.Lex, Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
        U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3,
        t4}))))), Lex.Lex{Lex.Idle{}, [], acc})), Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JBind{t1, t2, t3, t4}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Equal.cong(Lex.Lex, Lex.Lex, xx => Lex.run(String.to_list("}"), xx),
          Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))))),
          Lex.Lex{Lex.Idle{}, [], acc}), Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.quote(V.span.str(src, nn,
          U32.is_zero(nn))) ++ (":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))))),
          Lex.Lex{Lex.Idle{}, [], acc}),
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          M6.seq(Print.quote(V.span.str(src, nn, U32.is_zero(nn))),
          ":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))), Lex.Lex{Lex.Idle{}, [], acc},
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc},
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)), Equal.trans(Lex.Lex,
          Lex.run(String.to_list(":" ++ (Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4})))),
          Lex.Lex{Lex.Idle{}, [], Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4}))), Lex.Lex{Lex.Idle{},
          [], Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}),
          Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}), M6.seq(":",
          Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, {==}),
          Equal.trans(Lex.Lex, Lex.run(String.to_list(Print.print(vv) ++ ("," ++ Print.print(V.JBind{t1, t2, t3,
          t4}))), Lex.Lex{Lex.Idle{}, [], Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc}), Lex.run(String.to_list("," ++ Print.print(V.JBind{t1, t2, t3, t4})), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
          Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}),
          M6.seq(Print.print(vv), "," ++ Print.print(V.JBind{t1, t2, t3, t4}), Lex.Lex{Lex.Idle{}, [],
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc}, M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc), ih_v(v_ok)),
          M6.seq(",", Print.print(V.JBind{t1, t2, t3, t4}), M4.pend(vv,
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc),
          Lex.Lex{Lex.Idle{}, [], Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
              M4.close(vv, ',',
          Lex.TComma{}, {==}, Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc)))))), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
          Lex.run(String.to_list(Print.print(V.JBind{t1, t2, t3, t4})), Lex.Lex{Lex.Idle{}, [],
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)})),
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JBind{t1, t2, t3, t4},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JBind{t1, t2, t3, t4}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)}, ih_r(r_ok),
          Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, List.append(&2,
          Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JBind{t1, t2, t3, t4}, V.WObj{})),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)},
          Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(V.JBind{t1, t2, t3, t4},
          V.WObj{}), Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc))},
          Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> xx},
          List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(vv, V.WVal{}), Lex.TComma{} <> M3.tj(V.JBind{t1,
              t2,
          t3, t4}, V.WObj{})), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
          U32.is_zero(nn))))} <> acc), List.reverse.go(&2, Lex.Tok, M3.tj(V.JBind{t1, t2, t3, t4}, V.WObj{}),
          Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)),
              M7.rev_app(M3.tj(vv,
          V.WVal{}), Lex.TComma{} <> M3.tj(V.JBind{t1, t2, t3, t4}, V.WObj{}),
          Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn, U32.is_zero(nn))))} <> acc)))))

# the character lexer on a well-formed value's text
law lexp:
  for +val: V.Json
  for +sh: V.Shape
  for +h: {V.wf.go(val, sh) == True{} : Bool}
  for +acc: List<&2, Lex.Tok>
  lg(val, sh, acc)

def lexp(val, sh, h, acc):
  match val:
    case V.JNull{}:
      match sh:
        case V.WVal{}:
          {==}
        case V.WArr{}:
          M3.no(lg(V.JNull{}, V.WArr{}, acc), h)
        case V.WObj{}:
          M3.no(lg(V.JNull{}, V.WObj{}, acc), h)
    case V.JBool{bb}:
      match sh:
        case V.WVal{}:
          lexp_bool(bb, acc)
        case V.WArr{}:
          M3.no(lg(V.JBool{bb}, V.WArr{}, acc), h)
        case V.WObj{}:
          M3.no(lg(V.JBool{bb}, V.WObj{}, acc), h)
    case V.JNum{+raw}:
      match sh:
        case V.WVal{}:
          M2.lex_numl(String.to_list(raw), Equal.trans(Bool, D1.number(String.to_list(raw)), V.num.ok(raw), True{},
            Equal.sym(Bool, V.num.ok(raw), D1.number(String.to_list(raw)), L1.num_grammar(raw)), h), acc)
        case V.WArr{}:
          M3.no(lg(V.JNum{raw}, V.WArr{}, acc), h)
        case V.WObj{}:
          M3.no(lg(V.JNum{raw}, V.WObj{}, acc), h)
    case V.JStr{+txt}:
      match sh:
        case V.WVal{}:
          lex_quote(txt, acc)
        case V.WArr{}:
          M3.no(lg(V.JStr{txt}, V.WArr{}, acc), h)
        case V.WObj{}:
          M3.no(lg(V.JStr{txt}, V.WObj{}, acc), h)
    case V.JArr{+items}:
      match sh:
        case V.WVal{}:
          Equal.trans(Lex.Lex, Lex.run(String.to_list("[" ++ (Print.print(items) ++ "]")), Lex.Lex{Lex.Idle{}, [],
            acc}), Lex.run(String.to_list(Print.print(items) ++ "]"), Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc}),
              Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(items, V.WArr{}),
              [Lex.TCloseArr{}]), Lex.TOpenArr{} <> acc)}, M6.seq("[", Print.print(items) ++ "]", Lex.Lex{Lex.Idle{},
                  [],
              acc}, Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc}, {==}), Equal.trans(Lex.Lex,
              Lex.run(String.to_list(Print.print(items) ++ "]"), Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc}),
              Lex.run(String.to_list("]"), Lex.run(String.to_list(Print.print(items)), Lex.Lex{Lex.Idle{}, [],
              Lex.TOpenArr{} <> acc})), Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
              M3.tj(items, V.WArr{}), [Lex.TCloseArr{}]), Lex.TOpenArr{} <> acc)}, M6.run_app(Print.print(items), "]",
              Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc}), Equal.trans(Lex.Lex, Lex.run(String.to_list("]"),
              Lex.run(String.to_list(Print.print(items)), Lex.Lex{Lex.Idle{}, [], Lex.TOpenArr{} <> acc})),
              Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(items, V.WArr{}),
              Lex.TOpenArr{} <> acc)}, Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
              M3.tj(items, V.WArr{}), [Lex.TCloseArr{}]), Lex.TOpenArr{} <> acc)}, lexp(items, V.WArr{}, h,
              Lex.TOpenArr{} <> acc), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok,
              List.append(&2, Lex.Tok, M3.tj(items, V.WArr{}), [Lex.TCloseArr{}]), Lex.TOpenArr{} <> acc)},
              Lex.Lex{Lex.Idle{}, [], Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(items, V.WArr{}),
              Lex.TOpenArr{} <> acc)}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], xx},
              List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(items, V.WArr{}), [Lex.TCloseArr{}]),
              Lex.TOpenArr{} <> acc), Lex.TCloseArr{} <> List.reverse.go(&2, Lex.Tok, M3.tj(items, V.WArr{}),
              Lex.TOpenArr{} <> acc), M7.rev_app(M3.tj(items, V.WArr{}), [Lex.TCloseArr{}], Lex.TOpenArr{} <> acc))))))
        case V.WArr{}:
          M3.no(lg(V.JArr{items}, V.WArr{}, acc), h)
        case V.WObj{}:
          M3.no(lg(V.JArr{items}, V.WObj{}, acc), h)
    case V.JObj{+pairs}:
      match sh:
        case V.WVal{}:
          Equal.trans(Lex.Lex, Lex.run(String.to_list("{" ++ (Print.print(pairs) ++ "}")), Lex.Lex{Lex.Idle{}, [],
            acc}), Lex.run(String.to_list(Print.print(pairs) ++ "}"), Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}),
              Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(pairs, V.WObj{}),
              [Lex.TCloseObj{}]), Lex.TOpenObj{} <> acc)}, M6.seq("{", Print.print(pairs) ++ "}", Lex.Lex{Lex.Idle{},
                  [],
              acc}, Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}, {==}), Equal.trans(Lex.Lex,
              Lex.run(String.to_list(Print.print(pairs) ++ "}"), Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}),
              Lex.run(String.to_list("}"), Lex.run(String.to_list(Print.print(pairs)), Lex.Lex{Lex.Idle{}, [],
              Lex.TOpenObj{} <> acc})), Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
              M3.tj(pairs, V.WObj{}), [Lex.TCloseObj{}]), Lex.TOpenObj{} <> acc)}, M6.run_app(Print.print(pairs), "}",
              Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc}), Equal.trans(Lex.Lex, Lex.run(String.to_list("}"),
              Lex.run(String.to_list(Print.print(pairs)), Lex.Lex{Lex.Idle{}, [], Lex.TOpenObj{} <> acc})),
              Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(pairs, V.WObj{}),
              Lex.TOpenObj{} <> acc)}, Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok,
              M3.tj(pairs, V.WObj{}), [Lex.TCloseObj{}]), Lex.TOpenObj{} <> acc)}, lexp(pairs, V.WObj{}, h,
              Lex.TOpenObj{} <> acc), Equal.sym(Lex.Lex, Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok,
              List.append(&2, Lex.Tok, M3.tj(pairs, V.WObj{}), [Lex.TCloseObj{}]), Lex.TOpenObj{} <> acc)},
              Lex.Lex{Lex.Idle{}, [], Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(pairs, V.WObj{}),
              Lex.TOpenObj{} <> acc)}, Equal.cong(List<&2, Lex.Tok>, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], xx},
              List.reverse.go(&2, Lex.Tok, List.append(&2, Lex.Tok, M3.tj(pairs, V.WObj{}), [Lex.TCloseObj{}]),
              Lex.TOpenObj{} <> acc), Lex.TCloseObj{} <> List.reverse.go(&2, Lex.Tok, M3.tj(pairs, V.WObj{}),
              Lex.TOpenObj{} <> acc), M7.rev_app(M3.tj(pairs, V.WObj{}), [Lex.TCloseObj{}], Lex.TOpenObj{} <> acc))))))
        case V.WArr{}:
          M3.no(lg(V.JObj{pairs}, V.WArr{}, acc), h)
        case V.WObj{}:
          M3.no(lg(V.JObj{pairs}, V.WObj{}, acc), h)
    case V.JNil{}:
      match sh:
        case V.WVal{}:
          M3.no(lg(V.JNil{}, V.WVal{}, acc), h)
        case V.WArr{}:
          {==}
        case V.WObj{}:
          {==}
    case V.JCons{+hd, +tl}:
      match sh:
        case V.WVal{}:
          M3.no(lg(V.JCons{hd, tl}, V.WVal{}, acc), h)
        case V.WArr{}:
          lexp_cons(tl, hd, h, acc, xx => lexp(hd, V.WVal{}, xx, acc), xx => lexp(tl, V.WArr{}, xx,
            Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(hd, V.WVal{}), acc)))
        case V.WObj{}:
          M3.no(lg(V.JCons{hd, tl}, V.WObj{}, acc), h)
    case V.JPair{+kk, +vv, +rr}:
      match sh:
        case V.WVal{}:
          M3.no(lg(V.JPair{kk, vv, rr}, V.WVal{}, acc), h)
        case V.WArr{}:
          M3.no(lg(V.JPair{kk, vv, rr}, V.WArr{}, acc), h)
        case V.WObj{}:
          lexp_pair(rr, kk, vv, h, acc, xx => lexp(vv, V.WVal{}, xx,
            Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc), xx => lexp(rr, V.WObj{}, xx,
              Lex.TComma{} <> List.reverse.go(&2, Lex.Tok, M3.tj(vv, V.WVal{}),
              Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(kk))} <> acc)))
    case V.JSpan{+src, +nn}:
      match sh:
        case V.WVal{}:
          lex_quote(V.span.str(src, nn, U32.is_zero(nn)), acc)
        case V.WArr{}:
          M3.no(lg(V.JSpan{src, nn}, V.WArr{}, acc), h)
        case V.WObj{}:
          M3.no(lg(V.JSpan{src, nn}, V.WObj{}, acc), h)
    case V.JBind{+src, +nn, +vv, +rr}:
      match sh:
        case V.WVal{}:
          M3.no(lg(V.JBind{src, nn, vv, rr}, V.WVal{}, acc), h)
        case V.WArr{}:
          M3.no(lg(V.JBind{src, nn, vv, rr}, V.WArr{}, acc), h)
        case V.WObj{}:
          lexp_bind(rr, src, nn, vv, h, acc, xx => lexp(vv, V.WVal{}, xx,
            Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
            U32.is_zero(nn))))} <> acc), xx => lexp(rr, V.WObj{}, xx, Lex.TComma{} <> List.reverse.go(&2, Lex.Tok,
              M3.tj(vv, V.WVal{}), Lex.TColon{} <> Lex.TStr{M3.fixs(String.to_list(V.span.str(src, nn,
              U32.is_zero(nn))))} <> acc)))
