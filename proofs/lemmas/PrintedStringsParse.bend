# a printed string or value is read back by the character lexer
import Base
import ../../src/value.bend as V
import ../../src/lex.bend as Lex
import ../../src/print.bend as Print
import ../../laws/defs/CursorAndNumberRules.bend as D1
import ./CharacterClasses.bend as M1
import ./DenseTokens.bend as M2
import ./LexemeOrder.bend as M3
import ./LexerPunctuation.bend as M4
import ./LexingPrintedText.bend as M5

# fin_pend for a boolean
law fin_bool:
  for bb: Bool
  {Lex.finish(M4.pend(V.JBool{bb}, [])) == M3.tj(V.JBool{bb}, V.WVal{}) : List<&2, Lex.Tok>}

def fin_bool(bb):
  match bb:
    case True{}:
      {==}
    case False{}:
      {==}

# the end of a value's text closes its word, or leaves its tokens in order
law fin_pend:
  for +val: V.Json
  {Lex.finish(M4.pend(val, [])) == M3.tj(val, V.WVal{}) : List<&2, Lex.Tok>}

def fin_pend(val):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{bb}:
      fin_bool(bb)
    case V.JNum{+raw}:
      Equal.cong(String, List<&2, Lex.Tok>, xx => [Lex.TWord{xx}], Lex.text(List.reverse.go(&2, Char,
        String.to_list(raw), [])), raw,
        M3.word_text(raw))
    case V.JStr{+a1}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M3.tj(V.JStr{a1},
        V.WVal{}), []), []),
        List.append(&2, Lex.Tok, M3.tj(V.JStr{a1}, V.WVal{}), []), M3.tj(V.JStr{a1}, V.WVal{}),
            M2.rev_rev(M3.tj(V.JStr{a1},
          V.WVal{}), [], []), M2.lapp_nil(M3.tj(V.JStr{a1}, V.WVal{})))
    case V.JArr{+a1}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M3.tj(V.JArr{a1},
        V.WVal{}), []), []),
        List.append(&2, Lex.Tok, M3.tj(V.JArr{a1}, V.WVal{}), []), M3.tj(V.JArr{a1}, V.WVal{}),
            M2.rev_rev(M3.tj(V.JArr{a1},
          V.WVal{}), [], []), M2.lapp_nil(M3.tj(V.JArr{a1}, V.WVal{})))
    case V.JObj{+a1}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M3.tj(V.JObj{a1},
        V.WVal{}), []), []),
        List.append(&2, Lex.Tok, M3.tj(V.JObj{a1}, V.WVal{}), []), M3.tj(V.JObj{a1}, V.WVal{}),
            M2.rev_rev(M3.tj(V.JObj{a1},
          V.WVal{}), [], []), M2.lapp_nil(M3.tj(V.JObj{a1}, V.WVal{})))
    case V.JNil{}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M3.tj(V.JNil{},
          V.WVal{}),
        []), []),
        List.append(&2, Lex.Tok, M3.tj(V.JNil{}, V.WVal{}), []), M3.tj(V.JNil{}, V.WVal{}), M2.rev_rev(M3.tj(V.JNil{},
            V.WVal{}),
          [], []), M2.lapp_nil(M3.tj(V.JNil{}, V.WVal{})))
    case V.JCons{+a1, +a2}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M3.tj(V.JCons{a1, a2},
        V.WVal{}), []), []),
        List.append(&2, Lex.Tok, M3.tj(V.JCons{a1, a2}, V.WVal{}), []), M3.tj(V.JCons{a1, a2},
          V.WVal{}), M2.rev_rev(M3.tj(V.JCons{a1, a2}, V.WVal{}), [], []), M2.lapp_nil(M3.tj(V.JCons{a1, a2},
              V.WVal{})))
    case V.JPair{+a1, +a2, +a3}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M3.tj(V.JPair{a1, a2,
          a3},
        V.WVal{}), []), []),
        List.append(&2, Lex.Tok, M3.tj(V.JPair{a1, a2, a3}, V.WVal{}), []), M3.tj(V.JPair{a1, a2, a3},
          V.WVal{}), M2.rev_rev(M3.tj(V.JPair{a1, a2, a3}, V.WVal{}), [], []), M2.lapp_nil(M3.tj(V.JPair{a1, a2, a3},
              V.WVal{})))
    case V.JSpan{+a1, +a2}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M3.tj(V.JSpan{a1, a2},
        V.WVal{}), []), []),
        List.append(&2, Lex.Tok, M3.tj(V.JSpan{a1, a2}, V.WVal{}), []), M3.tj(V.JSpan{a1, a2},
          V.WVal{}), M2.rev_rev(M3.tj(V.JSpan{a1, a2}, V.WVal{}), [], []), M2.lapp_nil(M3.tj(V.JSpan{a1, a2},
              V.WVal{})))
    case V.JBind{+a1, +a2, +a3, +a4}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M3.tj(V.JBind{a1, a2, a3,
        a4}, V.WVal{}), []), []),
        List.append(&2, Lex.Tok, M3.tj(V.JBind{a1, a2, a3, a4}, V.WVal{}), []), M3.tj(V.JBind{a1, a2, a3, a4},
          V.WVal{}), M2.rev_rev(M3.tj(V.JBind{a1, a2, a3, a4}, V.WVal{}), [], []), M2.lapp_nil(M3.tj(V.JBind{a1, a2,
              a3, a4},
          V.WVal{})))

# WP-L2: the character lexer reads a well-formed value's text as its tokens
law lex_print:
  for +val: V.Json
  for h_wf: {V.wf(val) == True{} : Bool}
  {Lex.finish(Lex.run(String.to_list(Print.print(val)), Lex.Lex{Lex.Idle{}, [], []})) == M3.tj(val, V.WVal{}) : List<&2,
    Lex.Tok>}

def lex_print(val, h_wf):
  Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(Print.print(val)), Lex.Lex{Lex.Idle{}, [], []})),
    Lex.finish(M4.pend(val, [])), M3.tj(val, V.WVal{}),
    Equal.cong(Lex.Lex, List<&2, Lex.Tok>, xx => Lex.finish(xx), Lex.run(String.to_list(Print.print(val)),
      Lex.Lex{Lex.Idle{}, [], []}),
      M4.pend(val, []), M5.lexp(val, V.WVal{}, h_wf, [])),
    fin_pend(val))

# WP-L2: parse's lexer reads a well-formed value's text as its tokens, up to spans
law tokens_print:
  for +val: V.Json
  for h_wf: {V.wf(val) == True{} : Bool}
  for h_s: {D1.short(Print.print(val)) == True{} : Bool}
  {M3.dens(Lex.tokens(Print.print(val))) == M3.tj(val, V.WVal{}) : List<&2, Lex.Tok>}

def tokens_print(val, h_wf, h_s):
  +txt = Print.print(val)
  +lx = Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []}))
  Equal.trans(List<&2, Lex.Tok>, M3.dens(Lex.tokens(txt)), M3.dens(lx), M3.tj(val, V.WVal{}), M1.lexers_agree(txt, h_s),
    Equal.trans(List<&2, Lex.Tok>, M3.dens(lx), M3.dens(M3.tj(val, V.WVal{})), M3.tj(val, V.WVal{}),
      Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, xx => M3.dens(xx), lx, M3.tj(val, V.WVal{}), lex_print(val,
          h_wf)),
      M2.dens_tj(val, V.WVal{})))

# laws/QuotedStringReadsBack.bend: a printed string parses back

# a scalar value is its own fix
law fix_id:
  for +ch: Char
  for h_sc: {Bool.not(D1.non_scalar(Char.to_u32(ch))) == True{} : Bool}
  {M3.fix(ch) == ch : Char}

def fix_id(ch, h_sc):
  match ch:
    case Chr{+uu}:
      hs = Equal.sym(Bool, Bool.not(D1.non_scalar(uu)), True{}, h_sc)
      %hs : {Bool.pick(Char, _, Chr{uu}, Chr{65533}) == Chr{uu} : Char}
      {==}

# a text of scalar values is its own fix
law fixs_id:
  for +txt: String
  for +h_sc: {D1.scalars(txt) == True{} : Bool}
  {M3.fixs(String.to_list(txt)) == txt : String}

def fixs_id(txt, h_sc):
  match txt:
    case SNil{}:
      {==}
    case SCon{+hd, +tl}:
      +ok = Bool.not(D1.non_scalar(Char.to_u32(hd)))
      eh = fix_id(hd, M3.and_left(ok, D1.scalars(tl), h_sc))
      et = fixs_id(tl, M3.and_right(ok, D1.scalars(tl), h_sc))
      Equal.trans(String, SCon{M3.fix(hd), M3.fixs(String.to_list(tl))}, SCon{hd, M3.fixs(String.to_list(tl))},
          SCon{hd, tl},
        Equal.cong(Char, String, xx => SCon{xx, M3.fixs(String.to_list(tl))}, M3.fix(hd), hd, eh),
        Equal.cong(String, String, xx => SCon{hd, xx}, M3.fixs(String.to_list(tl)), tl, et))
