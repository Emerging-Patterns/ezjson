# proofs of laws/QuotedStringReadsBack.bend
import Base
import ../src/value.bend as V
import ../src/lex.bend as Lex
import ../src/parse.bend as Parse
import ../src/print.bend as Print
import ../laws/QuotedStringReadsBack.bend as Laws
import ../laws/defs/CursorAndNumberRules.bend as D1
import ./lemmas/LexemeOrder.bend as M1
import ./lemmas/PrintedStringsParse.bend as M2
import ./lemmas/StringTokens.bend as M3

def Laws.str_back(txt, h_sc, h_s):
  +got = M1.fixs(String.to_list(txt))
  Equal.trans(Maybe<&2, String>, D1.str_of(Parse.parse(Print.quote(txt))), Some{got}, Some{txt},
    M3.one_str(Lex.tokens(Print.quote(txt)), got, M2.tokens_print(V.JStr{txt}, {==}, h_s)),
    Equal.cong(String, Maybe<&2, String>, xx => Some{xx}, got, txt, M2.fixs_id(txt, h_sc)))
