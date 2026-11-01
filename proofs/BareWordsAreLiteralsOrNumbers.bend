# proofs of laws/BareWordsAreLiteralsOrNumbers.bend
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../src/lex.bend as Lex
import ../src/parse.bend as Parse
import ../laws/BareWordsAreLiteralsOrNumbers.bend as Laws
import ../laws/NumOkIsNumberRule.bend as L1
import ../laws/defs/CursorAndNumberRules.bend as D1
import ./lemmas/CharacterClasses.bend as M1
import ./lemmas/LexemeOrder.bend as M2
import ./lemmas/NumberDigits.bend as M3
import ./lemmas/OwnedParse.bend as M4
import ./lemmas/WordLexing.bend as M5

# laws/BareWordsAreLiteralsOrNumbers.bend: a bare word

# a word character is a word character to the lexer
law oth_wc:
  for +ch: Char
  for h: {D1.word_char(ch) == True{} : Bool}
  {Lex.classify(ch) == Lex.COther{} : Lex.Class}

def oth_wc(ch, h):
  match ch:
    case Chr{+uu}:
      M5.cls_by(Chr{uu}, xx => D1.word_char(Chr{xx}), h, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==}, {==},
        {==}, {==})

# word characters are word characters to the lexer
law oth_words:
  for +cs: List<&2, Char>
  for +h: {D1.word_chars(cs) == True{} : Bool}
  M5.others(cs)

def oth_words(cs, h):
  match cs:
    case Nil{}:
      Unit{}
    case +hd <> +tl:
      (oth_wc(hd, M2.and_left(D1.word_char(hd), D1.word_chars(tl), h)),
        oth_words(tl, M2.and_right(D1.word_char(hd), D1.word_chars(tl), h)))

# the character lexer reads a bare word as one word token
law bare_lex:
  for +txt: String
  for h_b: {D1.bare(txt) == True{} : Bool}
  {Lex.finish(Lex.run(String.to_list(txt), Lex.Lex{Lex.Idle{}, [], []})) == [Lex.TWord{txt}] : List<&2, Lex.Tok>}

def bare_lex(txt, h_b):
  match txt:
    case SNil{}:
      M2.no({Lex.finish(Lex.run(String.to_list(""), Lex.Lex{Lex.Idle{}, [], []})) == [Lex.TWord{""}] : List<&2,
          Lex.Tok>},
        h_b)
    case SCon{+hd, +tl}:
      +cs = String.to_list(SCon{hd, tl})
      Equal.trans(List<&2, Lex.Tok>, Lex.finish(Lex.run(cs, Lex.Lex{Lex.Idle{}, [], []})),
        Lex.finish(Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, cs, []), []}), [Lex.TWord{SCon{hd, tl}}],
        Equal.cong(Lex.Lex, List<&2, Lex.Tok>, zz => Lex.finish(zz), Lex.run(cs, Lex.Lex{Lex.Idle{}, [], []}),
          Lex.Lex{Lex.Word{}, List.reverse.go(&2, Char, cs, []), []}, M5.lex_word(hd, String.to_list(tl), oth_words(cs,
            h_b), [])),
        Equal.cong(String, List<&2, Lex.Tok>, zz => [Lex.TWord{zz}], Lex.text(List.reverse.go(&2, Char, cs, [])),
          SCon{hd, tl},
          M2.word_text(SCon{hd, tl})))

# parse's lexer reads a bare word as one word token, up to spans
law bare_toks:
  for +txt: String
  for h_b: {D1.bare(txt) == True{} : Bool}
  for h_s: {D1.short(txt) == True{} : Bool}
  {M2.dens(Lex.tokens(txt)) == [Lex.TWord{txt}] : List<&2, Lex.Tok>}

def bare_toks(txt, h_b, h_s):
  Equal.trans(List<&2, Lex.Tok>, M2.dens(Lex.tokens(txt)), M2.dens(Lex.finish(Lex.run(String.to_list(txt),
    Lex.Lex{Lex.Idle{}, [], []}))), [Lex.TWord{txt}], M1.lexers_agree(txt, h_s),
    Equal.cong(List<&2, Lex.Tok>, List<&2, Lex.Tok>, zz => M2.dens(zz), Lex.finish(Lex.run(String.to_list(txt),
      Lex.Lex{Lex.Idle{}, [], []})), [Lex.TWord{txt}], bare_lex(txt, h_b)))

# a lone word parses exactly when the parser accepts it
law wok:
  for ok: Bool
  for +txt: String
  {D1.is_some(Parse.finish(Parse.step.word.go(txt, Parse.P{False{}, None{}, Nil{}}, ok))) == ok : Bool}

def wok(ok, _txt):
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def Laws.bare_word(txt, h_b, h_s):
  Equal.trans(Bool, D1.is_some(Ezjson.parse(txt)), D1.is_some(D1.own_m(Parse.finish(Parse.run(Lex.tokens(txt),
    Parse.P{False{}, None{}, Nil{}})))), D1.lit_or_num(txt), Equal.sym(Bool,
    D1.is_some(D1.own_m(Parse.finish(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}})))),
    D1.is_some(Ezjson.parse(txt)),
    M2.some_own(Parse.finish(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}})))),
    Equal.trans(Bool, D1.is_some(D1.own_m(Parse.finish(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{},
      Nil{}})))), D1.is_some(Parse.finish(M4.ownp(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}})))),
      D1.lit_or_num(txt), Equal.cong(Maybe<&2, V.Json>, Bool, zz => D1.is_some(zz),
      D1.own_m(Parse.finish(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}}))),
    Parse.finish(M4.ownp(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}}))),
        M4.fin_own(Parse.run(Lex.tokens(txt),
      Parse.P{False{}, None{}, Nil{}}))),
    Equal.trans(Bool, D1.is_some(Parse.finish(M4.ownp(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}})))),
      D1.is_some(Parse.finish(Parse.run(M2.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}}))),
      D1.lit_or_num(txt), Equal.cong(Parse.P, Bool, zz => D1.is_some(Parse.finish(zz)),
      M4.ownp(Parse.run(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}})), Parse.run(M2.dens(Lex.tokens(txt)),
      Parse.P{False{}, None{}, Nil{}}),
    M4.run_own(Lex.tokens(txt), Parse.P{False{}, None{}, Nil{}})),
    Equal.trans(Bool, D1.is_some(Parse.finish(Parse.run(M2.dens(Lex.tokens(txt)), Parse.P{False{}, None{}, Nil{}}))),
      D1.is_some(Parse.finish(Parse.run([Lex.TWord{txt}], Parse.P{False{}, None{}, Nil{}}))), D1.lit_or_num(txt),
      Equal.cong(List<&2, Lex.Tok>, Bool, zz => D1.is_some(Parse.finish(Parse.run(zz, Parse.P{False{}, None{},
      Nil{}}))), M2.dens(Lex.tokens(txt)), [Lex.TWord{txt}],
    bare_toks(txt, h_b, h_s)),
    Equal.trans(Bool, D1.is_some(Parse.finish(Parse.run([Lex.TWord{txt}], Parse.P{False{}, None{}, Nil{}}))),
      Parse.word.ok(txt), D1.lit_or_num(txt), wok(Parse.word.ok(txt), txt),
    Equal.cong(Bool, Bool, zz => Bool.or(String.eq(txt, "null"), Bool.or(String.eq(txt, "true"), Bool.or(String.eq(txt,
    "false"), zz))), V.num.ok(txt), D1.number(String.to_list(txt)), L1.num_grammar(txt)))))))
