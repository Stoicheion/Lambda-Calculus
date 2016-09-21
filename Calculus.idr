module Calculus

||| Where "normal form" means no evaluation rules applies.
public export
data NormalForm = Value | Stuck

||| The result of evaluating a term is either another term or revealing no evaluation rule applies.
||| A "Reduction" is not necessarily "smaller" in some sense than the previous term nor is it
||| necessarily a different term.
public export
data Evaluation a = Reduction a | Termination NormalForm

public export
interface Calculus a where
  ||| One-step evaluation where the result specifies if termination was achieved.
  reduce1 : a -> Evaluation a

  ||| One-step evaluation.
  eval1 : a -> a
  eval1 t = case reduce1 t of
                 Reduction t' => t'
                 _ => t

  ||| Where "normal" means no evaluation rule applies.
  isNormal : a -> Bool
  isNormal t = case reduce1 t of
                    Termination _ => True
                    _ => False

  ||| "Is a value?" where "value" means no evaluation rule applies and "t" is not "stuck".
  isVal : a -> Bool
  isVal t = case reduce1 t of
                 Termination Value => True
                 _ => False

  ||| Where "stuck" means no evaluation rule applies and "t" is not a "value".
  isStuck : a -> Bool
  isStuck t = case reduce1 t of
              Termination Stuck => True
              _ => False

  partial
  stepByStep : Show a => a -> IO ()
  stepByStep t = do putStrLn currentTerm
                    putStrLn "Eval one step? (y/n)"
                    str <- getLine
                    case str of
                      "y" => do case reduce1 t of
                                    Reduction t' => stepByStep t'
                                    Termination Value => do putStrLn $ "Evaluator terminated with value:\n" ++ currentTerm
                                    Termination Stuck => do putStrLn $ "Evaluator became stuck with nonvalue:\n" ++ currentTerm
                      "n" => putStrLn "Done."
                      otherwise => stepByStep t
    where
    currentTerm : String
    currentTerm = "→" ++ show t
