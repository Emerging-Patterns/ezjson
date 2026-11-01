# proofs of laws/ReadersReadBuilders.bend
import Base
import ../src/value.bend as V
import ../main.bend as Ezjson
import ../laws/ReadersReadBuilders.bend as Laws

def Laws.as_bool_bool(_flag):
  {==}

def Laws.as_str_str(_txt):
  {==}

def Laws.as_num_num(txt, h_ok):
  ok = Equal.sym(Bool, V.num.ok(txt), True{}, h_ok)
  %ok : {Ezjson.as_num(V.num.go(txt, _)) == Some{txt} : Maybe<&2, String>}
  {==}
