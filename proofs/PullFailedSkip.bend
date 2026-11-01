# proofs of laws/PullFailedSkip.bend
import Base
import ../laws/PullFailedSkip.bend as Laws

def Laws.pull_failed_skip(_rest, _stack, done):
  match done:
    case True{}:
      {==}
    case False{}:
      {==}
