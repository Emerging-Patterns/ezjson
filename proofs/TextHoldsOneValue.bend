# proofs of laws/TextHoldsOneValue.bend
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../src/lex.bend as Lex
import ../src/parse.bend as Parse
import ../src/print.bend as Print
import ../laws/TextHoldsOneValue.bend as Laws
import ../laws/defs/CursorAndNumberRules.bend as D1
import ./lemmas/CanonicalValue.bend as M1
import ./lemmas/CharacterClasses.bend as M2
import ./lemmas/DenseTokens.bend as M3
import ./lemmas/LexemeOrder.bend as M4
import ./lemmas/LexerErrorSticks.bend as M5
import ./lemmas/LexerPunctuation.bend as M6
import ./lemmas/LexingPrintedText.bend as M7
import ./lemmas/OwnedParse.bend as M8
import ./lemmas/ParserReadsTokens.bend as M9
import ./lemmas/StringTokens.bend as M10

# laws/TextHoldsOneValue.bend: one value per text

# a space after a value's text pushes its tokens
law space_close:
  for +val: V.Json
  for +acc: List<&2, Lex.Tok>
  {Lex.feed(' ', M6.pend(val, acc)) == Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M4.tj(val, V.WVal{}),
    acc)} : Lex.Lex}

def space_close(val, acc):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{bb}:
      match bb:
        case True{}:
          {==}
        case False{}:
          {==}
    case V.JNum{+raw}:
      Equal.cong(String, Lex.Lex, xx => Lex.Lex{Lex.Idle{}, [], Lex.TWord{xx} <> acc},
        Lex.text(List.reverse.go(&2, Char, String.to_list(raw), [])), raw, M4.word_text(raw))
    case V.JStr{+a1}:
      {==}
    case V.JArr{+a1}:
      {==}
    case V.JObj{+a1}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+a1, +a2}:
      {==}
    case V.JPair{+a1, +a2, +a3}:
      {==}
    case V.JSpan{+a1, +a2}:
      {==}
    case V.JBind{+a1, +a2, +a3, +a4}:
      {==}

# the end of a value's text, on tokens already pushed
law fin_pend2:
  for +val: V.Json
  for +acc: List<&2, Lex.Tok>
  {Lex.finish(M6.pend(val, acc)) == List.reverse.go(&2, Lex.Tok, acc, M4.tj(val, V.WVal{})) : List<&2, Lex.Tok>}

def fin_pend2(val, acc):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{bb}:
      match bb:
        case True{}:
          {==}
        case False{}:
          {==}
    case V.JNum{+raw}:
      Equal.cong(String, List<&2, Lex.Tok>, xx => List.reverse.go(&2, Lex.Tok, acc, [Lex.TWord{xx}]),
        Lex.text(List.reverse.go(&2, Char, String.to_list(raw), [])), raw, M4.word_text(raw))
    case V.JStr{+a1}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M4.tj(V.JStr{a1},
        V.WVal{}), acc), []), List.reverse.go(&2, Lex.Tok, acc, List.append(&2, Lex.Tok, M4.tj(V.JStr{a1}, V.WVal{}),
        [])), List.reverse.go(&2, Lex.Tok, acc, M4.tj(V.JStr{a1}, V.WVal{})),
        M3.rev_rev(M4.tj(V.JStr{a1}, V.WVal{}), acc, []), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
          xx => List.reverse.go(&2, Lex.Tok, acc, xx), List.append(&2, Lex.Tok, M4.tj(V.JStr{a1}, V.WVal{}), []),
          M4.tj(V.JStr{a1}, V.WVal{}),
          M3.lapp_nil(M4.tj(V.JStr{a1}, V.WVal{}))))
    case V.JArr{+a1}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M4.tj(V.JArr{a1},
        V.WVal{}), acc), []), List.reverse.go(&2, Lex.Tok, acc, List.append(&2, Lex.Tok, M4.tj(V.JArr{a1}, V.WVal{}),
        [])), List.reverse.go(&2, Lex.Tok, acc, M4.tj(V.JArr{a1}, V.WVal{})),
        M3.rev_rev(M4.tj(V.JArr{a1}, V.WVal{}), acc, []), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
          xx => List.reverse.go(&2, Lex.Tok, acc, xx), List.append(&2, Lex.Tok, M4.tj(V.JArr{a1}, V.WVal{}), []),
          M4.tj(V.JArr{a1}, V.WVal{}),
          M3.lapp_nil(M4.tj(V.JArr{a1}, V.WVal{}))))
    case V.JObj{+a1}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M4.tj(V.JObj{a1},
        V.WVal{}), acc), []), List.reverse.go(&2, Lex.Tok, acc, List.append(&2, Lex.Tok, M4.tj(V.JObj{a1}, V.WVal{}),
        [])), List.reverse.go(&2, Lex.Tok, acc, M4.tj(V.JObj{a1}, V.WVal{})),
        M3.rev_rev(M4.tj(V.JObj{a1}, V.WVal{}), acc, []), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
          xx => List.reverse.go(&2, Lex.Tok, acc, xx), List.append(&2, Lex.Tok, M4.tj(V.JObj{a1}, V.WVal{}), []),
          M4.tj(V.JObj{a1}, V.WVal{}),
          M3.lapp_nil(M4.tj(V.JObj{a1}, V.WVal{}))))
    case V.JNil{}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M4.tj(V.JNil{},
          V.WVal{}),
        acc), []), List.reverse.go(&2, Lex.Tok, acc, List.append(&2, Lex.Tok, M4.tj(V.JNil{}, V.WVal{}), [])),
        List.reverse.go(&2, Lex.Tok, acc, M4.tj(V.JNil{}, V.WVal{})),
        M3.rev_rev(M4.tj(V.JNil{}, V.WVal{}), acc, []), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
          xx => List.reverse.go(&2, Lex.Tok, acc, xx), List.append(&2, Lex.Tok, M4.tj(V.JNil{}, V.WVal{}), []),
          M4.tj(V.JNil{}, V.WVal{}),
          M3.lapp_nil(M4.tj(V.JNil{}, V.WVal{}))))
    case V.JCons{+a1, +a2}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M4.tj(V.JCons{a1, a2},
        V.WVal{}), acc), []), List.reverse.go(&2, Lex.Tok, acc, List.append(&2, Lex.Tok, M4.tj(V.JCons{a1, a2},
            V.WVal{}),
        [])), List.reverse.go(&2, Lex.Tok, acc, M4.tj(V.JCons{a1, a2}, V.WVal{})),
        M3.rev_rev(M4.tj(V.JCons{a1, a2}, V.WVal{}), acc, []), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
          xx => List.reverse.go(&2, Lex.Tok, acc, xx), List.append(&2, Lex.Tok, M4.tj(V.JCons{a1, a2}, V.WVal{}), []),
          M4.tj(V.JCons{a1, a2}, V.WVal{}),
          M3.lapp_nil(M4.tj(V.JCons{a1, a2}, V.WVal{}))))
    case V.JPair{+a1, +a2, +a3}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M4.tj(V.JPair{a1, a2,
          a3},
        V.WVal{}), acc), []), List.reverse.go(&2, Lex.Tok, acc, List.append(&2, Lex.Tok, M4.tj(V.JPair{a1, a2, a3},
        V.WVal{}), [])), List.reverse.go(&2, Lex.Tok, acc, M4.tj(V.JPair{a1, a2, a3}, V.WVal{})),
        M3.rev_rev(M4.tj(V.JPair{a1, a2, a3}, V.WVal{}), acc, []), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
          xx => List.reverse.go(&2, Lex.Tok, acc, xx), List.append(&2, Lex.Tok, M4.tj(V.JPair{a1, a2, a3}, V.WVal{}),
              []),
          M4.tj(V.JPair{a1, a2, a3}, V.WVal{}),
          M3.lapp_nil(M4.tj(V.JPair{a1, a2, a3}, V.WVal{}))))
    case V.JSpan{+a1, +a2}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M4.tj(V.JSpan{a1, a2},
        V.WVal{}), acc), []), List.reverse.go(&2, Lex.Tok, acc, List.append(&2, Lex.Tok, M4.tj(V.JSpan{a1, a2},
            V.WVal{}),
        [])), List.reverse.go(&2, Lex.Tok, acc, M4.tj(V.JSpan{a1, a2}, V.WVal{})),
        M3.rev_rev(M4.tj(V.JSpan{a1, a2}, V.WVal{}), acc, []), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
          xx => List.reverse.go(&2, Lex.Tok, acc, xx), List.append(&2, Lex.Tok, M4.tj(V.JSpan{a1, a2}, V.WVal{}), []),
          M4.tj(V.JSpan{a1, a2}, V.WVal{}),
          M3.lapp_nil(M4.tj(V.JSpan{a1, a2}, V.WVal{}))))
    case V.JBind{+a1, +a2, +a3, +a4}:
      Equal.trans(List<&2, Lex.Tok>, List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M4.tj(V.JBind{a1, a2, a3,
        a4}, V.WVal{}), acc), []), List.reverse.go(&2, Lex.Tok, acc, List.append(&2, Lex.Tok, M4.tj(V.JBind{a1, a2, a3,
        a4}, V.WVal{}), [])), List.reverse.go(&2, Lex.Tok, acc, M4.tj(V.JBind{a1, a2, a3, a4}, V.WVal{})),
        M3.rev_rev(M4.tj(V.JBind{a1, a2, a3, a4}, V.WVal{}), acc, []), Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>,
          xx => List.reverse.go(&2, Lex.Tok, acc, xx), List.append(&2, Lex.Tok, M4.tj(V.JBind{a1, a2, a3, a4},
              V.WVal{}),
          []), M4.tj(V.JBind{a1, a2, a3, a4}, V.WVal{}),
          M3.lapp_nil(M4.tj(V.JBind{a1, a2, a3, a4}, V.WVal{}))))

# a word, once a root is finished, raises the error flag
law nb_word:
  for ok: Bool
  for +raw: String
  for +cc: V.Json
  {M5.pbad(Parse.step.word.go(raw, Parse.P{False{}, Some{cc}, Nil{}}, ok)) == True{} : Bool}

def nb_word(ok, _raw, _cc):
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# after a finished root, a value's first token raises the error flag
law after_root:
  for +val: V.Json
  for +cc: V.Json
  for h: {V.wf(val) == True{} : Bool}
  {M5.pbad(Parse.step(M2.thead(M4.tj(val, V.WVal{})), Parse.P{False{}, Some{cc}, Nil{}})) == True{} : Bool}

def after_root(val, cc, h):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{bb}:
      match bb:
        case True{}:
          {==}
        case False{}:
          {==}
    case V.JNum{+raw}:
      nb_word(Parse.word.ok(raw), raw, cc)
    case V.JStr{+a1}:
      {==}
    case V.JArr{+a1}:
      {==}
    case V.JObj{+a1}:
      {==}
    case V.JNil{}:
      {==}
    case V.JCons{+a1, +a2}:
      M4.no({M5.pbad(Parse.step(M2.thead(M4.tj(V.JCons{a1, a2}, V.WVal{})), Parse.P{False{}, Some{cc},
          Nil{}})) == True{} : Bool},
        h)
    case V.JPair{+a1, +a2, +a3}:
      M4.no({M5.pbad(Parse.step(M2.thead(M4.tj(V.JPair{a1, a2, a3}, V.WVal{})), Parse.P{False{}, Some{cc},
        Nil{}})) == True{} : Bool}, h)
    case V.JSpan{+a1, +a2}:
      {==}
    case V.JBind{+a1, +a2, +a3, +a4}:
      M4.no({M5.pbad(Parse.step(M2.thead(M4.tj(V.JBind{a1, a2, a3, a4}, V.WVal{})), Parse.P{False{}, Some{cc},
        Nil{}})) == True{} : Bool}, h)

# a nonempty token list whose first token raises the error flag does not parse
law rej_after:
  for xs: List<&2, Lex.Tok>
  for +st: Parse.P
  for ne: {M2.tnil(xs) == False{} : Bool}
  for h: {M5.pbad(Parse.step(M2.thead(xs), st)) == True{} : Bool}
  {Parse.finish(Parse.run(xs, st)) == None{} : Maybe<&2, V.Json>}

def rej_after(xs, st, ne, h):
  match xs:
    case Nil{}:
      M4.no({Parse.finish(st) == None{} : Maybe<&2, V.Json>}, Equal.sym(Bool, True{}, False{}, ne))
    case +tok <> +rest:
      M5.fin_bad(Parse.run(rest, Parse.step(tok, st)), M5.run_bad(rest, Parse.step(tok, st), h))

# a well-formed value has tokens
law tj_ne:
  for +val: V.Json
  for h: {V.wf(val) == True{} : Bool}
  {M2.tnil(M4.tj(val, V.WVal{})) == False{} : Bool}

def tj_ne(val, h):
  match val:
    case V.JNull{}:
      {==}
    case V.JBool{bb}:
      match bb:
        case True{}:
          {==}
        case False{}:
          {==}
    case V.JNum{+raw}:
      {==}
    case V.JStr{+a1}:
      {==}
    case V.JArr{+a1}:
      {==}
    case V.JObj{+a1}:
      {==}
    case V.JNil{}:
      M4.no({M2.tnil(M4.tj(V.JNil{}, V.WVal{})) == False{} : Bool}, h)
    case V.JCons{+a1, +a2}:
      M4.no({M2.tnil(M4.tj(V.JCons{a1, a2}, V.WVal{})) == False{} : Bool}, h)
    case V.JPair{+a1, +a2, +a3}:
      M4.no({M2.tnil(M4.tj(V.JPair{a1, a2, a3}, V.WVal{})) == False{} : Bool}, h)
    case V.JSpan{+a1, +a2}:
      {==}
    case V.JBind{+a1, +a2, +a3, +a4}:
      M4.no({M2.tnil(M4.tj(V.JBind{a1, a2, a3, a4}, V.WVal{})) == False{} : Bool}, h)

# the character lexer on two values' text, a space between
law two_lex:
  for +jj: V.Json
  for +kk: V.Json
  for +h_j: {V.wf(jj) == True{} : Bool}
  for +h_k: {V.wf(kk) == True{} : Bool}
  {Lex.finish(Lex.run(String.to_list(Print.print(jj) ++ " " ++ Print.print(kk)), Lex.Lex{Lex.Idle{}, [],
    []})) == List.append(&2, Lex.Tok, M4.tj(jj, V.WVal{}), M4.tj(kk, V.WVal{})) : List<&2, Lex.Tok>}

def two_lex(jj, kk, h_j, h_k):
  Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(Print.print(jj) ++ " " ++ Print.print(kk)),
    Lex.Lex{Lex.Idle{}, [], []})), Lex.finish(Lex.run(String.to_list(" " ++ Print.print(kk)), M6.pend(jj, []))),
    List.append(&2, Lex.Tok, M4.tj(jj, V.WVal{}), M4.tj(kk, V.WVal{})), Equal.cong(Lex.Lex, List<&2, Lex.Tok>,
    zz => Lex.finish(zz), Lex.run(String.to_list(Print.print(jj) ++ " " ++ Print.print(kk)), Lex.Lex{Lex.Idle{}, [],
    []}),
    Lex.run(String.to_list(" " ++ Print.print(kk)), M6.pend(jj, [])), M10.seq(Print.print(jj), " " ++ Print.print(kk),
      Lex.Lex{Lex.Idle{}, [], []}, M6.pend(jj, []), M7.lexp(jj, V.WVal{}, h_j, []))),
    Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(" " ++ Print.print(kk)), M6.pend(jj, []))),
      Lex.finish(Lex.run(String.to_list(Print.print(kk)), Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M4.tj(jj,
      V.WVal{}), [])})), List.append(&2, Lex.Tok, M4.tj(jj, V.WVal{}), M4.tj(kk, V.WVal{})), Equal.cong(Lex.Lex,
          List<&2,
      Lex.Tok>, zz => Lex.finish(zz), Lex.run(String.to_list(" " ++ Print.print(kk)), M6.pend(jj, [])),
    Lex.run(String.to_list(Print.print(kk)), Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok, M4.tj(jj, V.WVal{}),
      [])}), M10.seq(" ", Print.print(kk), M6.pend(jj, []), Lex.Lex{Lex.Idle{}, [], List.reverse.go(&2, Lex.Tok,
          M4.tj(jj,
      V.WVal{}), [])},
      space_close(jj, []))),
    Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(String.to_list(Print.print(kk)), Lex.Lex{Lex.Idle{}, [],
      List.reverse.go(&2, Lex.Tok, M4.tj(jj, V.WVal{}), [])})), Lex.finish(M6.pend(kk, List.reverse.go(&2, Lex.Tok,
          M4.tj(jj,
      V.WVal{}), []))), List.append(&2, Lex.Tok, M4.tj(jj, V.WVal{}), M4.tj(kk, V.WVal{})), Equal.cong(Lex.Lex, List<&2,
      Lex.Tok>, zz => Lex.finish(zz), Lex.run(String.to_list(Print.print(kk)), Lex.Lex{Lex.Idle{}, [],
      List.reverse.go(&2, Lex.Tok, M4.tj(jj, V.WVal{}), [])}),
    M6.pend(kk, List.reverse.go(&2, Lex.Tok, M4.tj(jj, V.WVal{}), [])), M7.lexp(kk, V.WVal{}, h_k, List.reverse.go(&2,
        Lex.Tok,
      M4.tj(jj, V.WVal{}), []))),
    Equal.trans(List<&2, Lex.Tok>, Lex.finish(M6.pend(kk, List.reverse.go(&2, Lex.Tok, M4.tj(jj, V.WVal{}), []))),
      List.reverse.go(&2, Lex.Tok, List.reverse.go(&2, Lex.Tok, M4.tj(jj, V.WVal{}), []), M4.tj(kk, V.WVal{})),
      List.append(&2, Lex.Tok, M4.tj(jj, V.WVal{}), M4.tj(kk, V.WVal{})), fin_pend2(kk, List.reverse.go(&2, Lex.Tok,
          M4.tj(jj,
      V.WVal{}), [])),
    M3.rev_rev(M4.tj(jj, V.WVal{}), [], M4.tj(kk, V.WVal{}))))))

def Laws.two_none(jj, kk, h_j, h_k, h_s):
  M5.own_m_none(Ezjson.parse(Print.print(jj) ++ " " ++ Print.print(kk)),
    Equal.trans(Maybe<&2, V.Json>,
      D1.own_m(Parse.finish(Parse.run(Lex.tokens(Print.print(jj) ++ " " ++ Print.print(kk)), Parse.P{False{}, None{},
      Nil{}}))), Parse.finish(M8.ownp(Parse.run(Lex.tokens(Print.print(jj) ++ " " ++ Print.print(kk)), Parse.P{False{},
      None{}, Nil{}}))), None{}, M8.fin_own(Parse.run(Lex.tokens(Print.print(jj) ++ " " ++ Print.print(kk)),
      Parse.P{False{}, None{}, Nil{}})),
      Equal.trans(Maybe<&2, V.Json>,
          Parse.finish(M8.ownp(Parse.run(Lex.tokens(Print.print(jj) ++ " " ++ Print.print(kk)),
        Parse.P{False{}, None{}, Nil{}}))),
        Parse.finish(Parse.run(M4.dens(Lex.tokens(Print.print(jj) ++ " " ++ Print.print(kk))), Parse.P{False{}, None{},
        Nil{}})), None{}, Equal.cong(Parse.P, Maybe<&2, V.Json>, zz => Parse.finish(zz),
        M8.ownp(Parse.run(Lex.tokens(Print.print(jj) ++ " " ++ Print.print(kk)), Parse.P{False{}, None{}, Nil{}})),
        Parse.run(M4.dens(Lex.tokens(Print.print(jj) ++ " " ++ Print.print(kk))), Parse.P{False{}, None{}, Nil{}}),
      M8.run_own(Lex.tokens(Print.print(jj) ++ " " ++ Print.print(kk)), Parse.P{False{}, None{}, Nil{}})),
      Equal.trans(Maybe<&2, V.Json>,
        Parse.finish(Parse.run(M4.dens(Lex.tokens(Print.print(jj) ++ " " ++ Print.print(kk))), Parse.P{False{}, None{},
        Nil{}})),
        Parse.finish(Parse.run(M4.dens(Lex.finish(Lex.run(String.to_list(Print.print(jj) ++ " " ++ Print.print(kk)),
        Lex.Lex{Lex.Idle{}, [], []}))), Parse.P{False{}, None{}, Nil{}})), None{}, Equal.cong(List<&2, Lex.Tok>,
        Maybe<&2, V.Json>, zz => Parse.finish(Parse.run(zz, Parse.P{False{}, None{}, Nil{}})),
        M4.dens(Lex.tokens(Print.print(jj) ++ " " ++ Print.print(kk))),
        M4.dens(Lex.finish(Lex.run(String.to_list(Print.print(jj) ++ " " ++ Print.print(kk)), Lex.Lex{Lex.Idle{}, [],
        []}))), M2.lexers_agree(Print.print(jj) ++ " " ++ Print.print(kk), h_s)),
      Equal.trans(Maybe<&2, V.Json>,
        Parse.finish(Parse.run(M4.dens(Lex.finish(Lex.run(String.to_list(Print.print(jj) ++ " " ++ Print.print(kk)),
        Lex.Lex{Lex.Idle{}, [], []}))), Parse.P{False{}, None{}, Nil{}})),
            Parse.finish(Parse.run(M4.dens(List.append(&2,
        Lex.Tok, M4.tj(jj, V.WVal{}), M4.tj(kk, V.WVal{}))), Parse.P{False{}, None{}, Nil{}})), None{},
            Equal.cong(List<&2,
        Lex.Tok>, Maybe<&2, V.Json>, zz => Parse.finish(Parse.run(M4.dens(zz), Parse.P{False{}, None{}, Nil{}})),
        Lex.finish(Lex.run(String.to_list(Print.print(jj) ++ " " ++ Print.print(kk)), Lex.Lex{Lex.Idle{}, [], []})),
        List.append(&2, Lex.Tok, M4.tj(jj, V.WVal{}), M4.tj(kk, V.WVal{})), two_lex(jj, kk, h_j, h_k)),
      Equal.trans(Maybe<&2, V.Json>, Parse.finish(Parse.run(M4.dens(List.append(&2, Lex.Tok, M4.tj(jj, V.WVal{}),
          M4.tj(kk,
        V.WVal{}))), Parse.P{False{}, None{}, Nil{}})), Parse.finish(Parse.run(List.append(&2, Lex.Tok, M4.tj(jj,
        V.WVal{}), M4.tj(kk, V.WVal{})), Parse.P{False{}, None{}, Nil{}})), None{}, Equal.cong(List<&2, Lex.Tok>,
        Maybe<&2, V.Json>, zz => Parse.finish(Parse.run(zz, Parse.P{False{}, None{}, Nil{}})), M4.dens(List.append(&2,
        Lex.Tok, M4.tj(jj, V.WVal{}), M4.tj(kk, V.WVal{}))), List.append(&2, Lex.Tok, M4.tj(jj, V.WVal{}), M4.tj(kk,
            V.WVal{})),
      Equal.trans(List<&2, Lex.Tok>, M4.dens(List.append(&2, Lex.Tok, M4.tj(jj, V.WVal{}), M4.tj(kk, V.WVal{}))),
        List.append(&2, Lex.Tok, M4.dens(M4.tj(jj, V.WVal{})), M4.dens(M4.tj(kk, V.WVal{}))), List.append(&2, Lex.Tok,
            M4.tj(jj,
        V.WVal{}), M4.tj(kk, V.WVal{})),
        M2.dens_app(M4.tj(jj, V.WVal{}), M4.tj(kk, V.WVal{})),
        M3.app_cong(M4.dens(M4.tj(jj, V.WVal{})), M4.tj(jj, V.WVal{}), M4.dens(M4.tj(kk, V.WVal{})), M4.tj(kk,
            V.WVal{}), M3.dens_tj(jj,
          V.WVal{}),
          M3.dens_tj(kk, V.WVal{})))),
      Equal.trans(Maybe<&2, V.Json>, Parse.finish(Parse.run(List.append(&2, Lex.Tok, M4.tj(jj, V.WVal{}), M4.tj(kk,
        V.WVal{})), Parse.P{False{}, None{}, Nil{}})), Parse.finish(Parse.run(M4.tj(kk, V.WVal{}), Parse.run(M4.tj(jj,
        V.WVal{}), Parse.P{False{}, None{}, Nil{}}))), None{}, Equal.cong(Parse.P, Maybe<&2, V.Json>,
        zz => Parse.finish(zz), Parse.run(List.append(&2, Lex.Tok, M4.tj(jj, V.WVal{}), M4.tj(kk, V.WVal{})),
        Parse.P{False{}, None{}, Nil{}}),
      Parse.run(M4.tj(kk, V.WVal{}), Parse.run(M4.tj(jj, V.WVal{}), Parse.P{False{}, None{}, Nil{}})),
          M9.prun_app(M4.tj(jj,
        V.WVal{}), M4.tj(kk, V.WVal{}), Parse.P{False{}, None{}, Nil{}})),
      Equal.trans(Maybe<&2, V.Json>, Parse.finish(Parse.run(M4.tj(kk, V.WVal{}), Parse.run(M4.tj(jj, V.WVal{}),
        Parse.P{False{}, None{}, Nil{}}))), Parse.finish(Parse.run(M4.tj(kk, V.WVal{}), Parse.P{False{},
            Some{M1.canon(jj,
        V.WVal{})}, Nil{}})), None{}, Equal.cong(Parse.P, Maybe<&2, V.Json>, zz => Parse.finish(Parse.run(M4.tj(kk,
        V.WVal{}), zz)), Parse.run(M4.tj(jj, V.WVal{}), Parse.P{False{}, None{}, Nil{}}),
      Parse.P{False{}, Some{M1.canon(jj, V.WVal{})}, Nil{}}, M1.pv_top(jj, h_j)),
      rej_after(M4.tj(kk, V.WVal{}), Parse.P{False{}, Some{M1.canon(jj, V.WVal{})}, Nil{}}, tj_ne(kk, h_k),
          after_root(kk,
        M1.canon(jj, V.WVal{}), h_k))))))))))
