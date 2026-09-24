# bolt.bend: how bolt lints this repo. Every rule is an error except the law
# rules, which warn while every law in ezjson/LAWS.bend is still closed. The
# SPEC.md change turns `closed` and `trace` to error (docs/rfc/ezjson-spec.md,
# Rollout). See bolt/config.bend for the groups and levels.
import Base

# what will fail or blow up
def correctness() -> String:
  "error"

# what is probably a slip
def suspicious() -> String:
  "error"

# comments and whitespace
def style() -> String:
  "error"

# a def named by no quantified law, a law with no binder: advice until the
# closed laws are replaced
def laws() -> String:
  "warn"
