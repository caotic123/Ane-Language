import AneParser
import Data.Bool
import Data.HashMap

data Correctly = Yes | No deriving Show
data Assumptions = Assume_Equal String String Correctly | Assume_Reducible String Correctly |Assume_Finish String Correctly deriving Show

data Erros = Erros [String] deriving Show
data State = State [Assumptions] Erros deriving Show

there_term :: Definition -> String -> Bool
there_term (Definition y m k) x = member x m

substituteByidenty :: TermBody -> (Map String VarUnit) -> VarUnit -> TermBody
substituteByidenty k m i = case k of
                         (LambdaTerm ks) -> (transform_identy_lambda (LambdaTerm ks) m i)
                         (FreeVar p) -> case p of
                                          VarName ls -> if (member ls m) then (FreeVar (VarCode (m ! ls))) else (FreeVar p)
                                          VarCode ls -> (FreeVar p)
                         (App a a_) -> (App (substituteByidenty a m i) (substituteByidenty a_ m i)) 


transform_identy_lambda :: TermBody -> (Map String VarUnit) -> VarUnit -> TermBody
transform_identy_lambda k m i__ = case k of
                                  (LambdaTerm (Lam (VarName y) k)) -> LambdaTerm (Lam (VarCode i__) (substituteByidenty k (insert y i__ m) (X i__)))                 
                                  (App a a_) -> (App (transform_identy_lambda a m i__) (transform_identy_lambda a_ m i__))
                                  _ -> k

getTermLambda :: String -> Term -> Maybe Lambda
getTermLambda x y = (Data.HashMap.lookup x y)

isCorrect :: Bool -> Correctly
isCorrect k = bool No Yes k

lambda_identy k = transform_identy_lambda k empty I

safe_head :: [a] -> Maybe a
safe_head xs = case xs of
                 (x : xs_) -> Just x
                 _ -> Nothing

equalIsCorrect :: (String, String) -> (Lambda, Lambda) -> State -> State
equalIsCorrect (t, t_) ((Lambda k), (Lambda d)) (State y s) = State ((Assume_Equal t t_  (isCorrect ((lambda_identy k) == (lambda_identy d)) )) : y) s

isLambaTermAllApplicable :: TermBody -> Bool
isLambaTermAllApplicable k = case lambda_identy k of
                                       (LambdaTerm (Lam y k)) -> isLambaTermAllApplicable k 
                                       (App y x) -> (isLambaTermAllApplicable y) && (isLambaTermAllApplicable x)
                                       (FreeVar x) -> case x of
                                                        VarName y -> (if y == "*" then True else False)
                                                        VarCode y -> True
isTermReducible :: String -> Term -> State -> State
isTermReducible k term (State y (Erros s)) = case (getTermLambda k term) of
                                  Just (Lambda x) -> (State ((Assume_Reducible k (isCorrect (isLambaTermAllApplicable x))) : y) (Erros s))
                                  Nothing -> (State y (Erros ((("Term " ++ k ++ "Dont Found trying assume Reducible")  : s))))
hasSameName x y = case (x, y) of
                    (VarName x, VarName y) -> (x == y)
                    _ -> False 

substituteTermLambda :: TermBody -> (Var, TermBody) -> TermBody 
substituteTermLambda x (t, y) = case x of
                                 (LambdaTerm (Lam a z)) -> (LambdaTerm (Lam a (bool (substituteTermLambda z (t, y)) z (hasSameName a t))))
                                 (App a a_) -> (App (substituteTermLambda a (t, y)) (substituteTermLambda a_ (t, y)))
                                 (FreeVar p) -> bool (FreeVar p) y (hasSameName t p)

deriveLambdaFunction :: TermBody -> Maybe TermBody
deriveLambdaFunction k = case k of
                          (LambdaTerm y) -> Just(LambdaTerm y)
                          _ -> Nothing

getVarIdentyName :: Var -> String
getVarIdentyName c = case c of
                       (VarName y) -> y
                       _ -> "?"

betaReduction :: TermBody -> (Var, TermBody) -> Either String TermBody
betaReduction x (y, k) = do
                           let error_beta = "Term can't be applicable for beta reduction in " ++ (getVarIdentyName y)
                           case x of
                             LambdaTerm (Lam a b) -> if (hasSameName a y) then (case (deriveLambdaFunction (substituteTermLambda b (y, k))) of
                                                                                  Just x -> Right x
                                                                                  Nothing -> Left "Can't derive beta reduction because the term reduces in a non-function"
                                                                               )
                                                    else Left error_beta
                             _ -> Left error_beta

getTermByTermOrLambda :: Term -> TermOrLambda -> Maybe TermBody
getTermByTermOrLambda r s = case s of
                            VarTerm x -> case (getTermLambda x r) of
                                           Just (Lambda y) -> Just y
                                           Nothing -> Nothing
                            VarLambda (Lambda y) -> Just y

getTermBodyByLambda :: Lambda -> TermBody            
getTermBodyByLambda(Lambda k) = k

applyBetaReduction :: Definition -> State -> (String, String, TermOrLambda) -> (Definition, State)
applyBetaReduction (Definition k terms (yy : y)) (State a (Erros s)) (term_name, var_name, l) = do
     let get_term_lambda_name k = case k of
                                          VarTerm x -> x
                                          VarLambda _ -> ""

     case ((getTermByTermOrLambda terms l), (getTermLambda term_name terms)) of
        (Just x_, Just (Lambda y_)) -> case (betaReduction y_ ((VarName var_name), x_)) of
                                Right x -> ((Definition k (insert term_name (Lambda x) terms) y), (State a (Erros s)))
                                Left y_ -> ((Definition k terms y), (State a (Erros (y_ : s))))
        (Nothing, Just _) -> ((Definition k terms y), (State a (Erros (("Term " ++ (get_term_lambda_name l) ++ " don't found trying apply beta reduction") : s))))
        _ -> ((Definition k terms y), (State a (Erros (("Term " ++ var_name ++ " don't found trying apply beta reduction") : s))))

applicationLambda :: TermBody -> TermBody
applicationLambda k = case k of
                    (App a a_) -> case a of
                                    (LambdaTerm (Lam n x)) -> substituteTermLambda x (n, a_)
                                    _ -> (App a a_)
                    _ -> k

applyInLambda :: TermBody -> TermBody
applyInLambda t = case t of
                    (LambdaTerm (Lam x y)) -> (LambdaTerm (Lam x (applyInLambda y)))
                    (App a a_) -> applicationLambda (App (applyInLambda a) (applyInLambda a_))
                    (FreeVar x) -> (FreeVar x) 

applyWholeApplicationInTerm :: Definition -> State -> String -> (Definition, State)
applyWholeApplicationInTerm (Definition k terms (yy : y)) (State a (Erros s)) ny = 
   case (getTermLambda ny terms) of
     Just (Lambda x) -> ((Definition k (insert ny (Lambda (applyInLambda x)) terms) y), (State a (Erros s)))
     Nothing -> ((Definition k terms y), (State a (Erros (("Term " ++ ny ++ " don't found trying apply beta reduction") : s))))

applyTerms :: TermBody -> Term -> TermBody
applyTerms k term = case k of
                 (LambdaTerm (Lam x y)) -> (LambdaTerm (Lam x (applyTerms y term)))
                 (App a a_) -> (App (applyTerms a term) (applyTerms a_ term))
                 (FreeVar y) -> case (getTermLambda (getVarIdentyName y) term) of
                                  Just (Lambda x) -> x
                                  Nothing -> (FreeVar y) 
    
applyTermsInLambaTerm :: Definition -> State -> String -> (Definition, State)
applyTermsInLambaTerm (Definition k terms (yy : y)) (State a (Erros s)) kk = 
   case (getTermLambda kk terms) of
      Just (Lambda x) -> ((Definition k (insert kk (Lambda (applyTerms x terms)) terms) y), (State a (Erros s)))
      Nothing -> ((Definition k terms y), (State a (Erros (("Term " ++ kk ++ " don't found trying apply beta reduction") : s))))

checkMFinish :: [(Maybe TermBody, Maybe TermBody)] -> Lambda -> Bool
checkMFinish [] _ = True
checkMFinish ((_, Nothing) : xs) y = False
checkMFinish ((Nothing, _) : xs) y = False
checkMFinish (((Just x), (Just x_)) : xs) y = case y of
                              (Lambda (LambdaTerm (Lam n fx))) -> case betaReduction (LambdaTerm (Lam n fx)) (n, x) of
                                                                    Right f -> (lambda_identy (applyInLambda f) == lambda_identy (applyInLambda x_)) && checkMFinish xs y
                                                                    Left _ -> False
                              _ -> False

checkFinish :: Definition -> State -> Finish -> Either String (Definition, State)
checkFinish (Definition x_ terms (yy : y)) (State a (Erros s)) xy = do
                                              let simply_finish y k x = (Assume_Finish y (isCorrect ((lambda_identy k) == (lambda_identy x)))) : a
                                              let pairTermToLambda y = Prelude.map (\(x, y) -> ((getTermByTermOrLambda terms x), (getTermByTermOrLambda terms y))) y
                                              case (getTermLambda x_ terms) of 
                                                Just (Lambda x) -> case xy of
                                                   Finish w -> case (getTermByTermOrLambda terms w) of
                                                                 Just (LambdaTerm w) -> Right ((Definition x_ terms y), (State (simply_finish x_ (LambdaTerm w) x) (Erros s)))
                                                                 _ -> Left ("Your term" ++ x_  ++ "is a lambda func?")
                                                   MFinish t -> case (checkMFinish (pairTermToLambda t) (Lambda x)) of  
                                                      True -> Right ((Definition x_ terms y), (State ((Assume_Finish x_ Yes) : a) (Erros s)))   
                                                      False -> Left "Terms aren't equals"
                                                Nothing -> Left "Your definition has last term?"
                                                

--applyFinishTerm :: Definition -> State -> Finish -> (Definition, State)
--applyTermsInLambaTerm (Definition k terms (yy : y)) (State a (Erros s)) fi = 


applyOperarations :: (Definition, State) -> (Definition, State)
applyOperarations ((Definition k terms []), b) = ((Definition k terms []), b)
applyOperarations ((Definition k terms (z : zs)), (State a (Erros s))) = applyOperarations (case z of
                                                     Equal (x, y) -> case getTermLambda x terms of
                                                                       Just x_ -> case getTermLambda y terms of
                                                                          Just y_ -> ((Definition k terms zs), equalIsCorrect (x, y) (x_, y_) (State a (Erros s)))
                                                                          Nothing -> ((Definition k terms zs), (State a (Erros ((("Term " ++ y ++ "Dont Found trying Equality")  : s)))))
                                                                       Nothing -> ((Definition k terms zs), (State a (Erros ((("Term " ++ x ++ "Dont Found trying Equality")  : s)))))
                                                     BetaReduction y -> applyBetaReduction (Definition k terms (z : zs)) (State a (Erros s)) y
                                                     NoHasSideVar x -> ((Definition k terms zs), isTermReducible x terms (State a (Erros s)))
                                                     Apply x -> applyWholeApplicationInTerm (Definition k terms (z : zs)) (State a (Erros s)) x
                                                     ApplyTerms y -> applyTermsInLambaTerm (Definition k terms (z : zs)) (State a (Erros s)) y
                                                     CheckFinish h -> case (checkFinish (Definition k terms (z : zs)) (State a (Erros s)) h) of
                                                                        Right x -> x
                                                                        Left a_ -> ((Definition k terms zs), (State a (Erros (a_ : s))))
                                                     _ -> ((Definition k terms zs), (State a (Erros s))))

printState :: State -> IO ()
printState (State a (Erros [])) = return ()
printState (State a (Erros (x : xs))) = putStrLn x >> printState (State a (Erros xs))

main = do
         let tests (AST ((Definition x z k) : xs)) = do
                                                     let lambda (Lambda k) = k
                                                     lambda (z ! "retx") 
         let test (AST ((Definition x z k) : xs)) = (Definition x z k)
         n <- readFile "ane.ane"
         case (getAneAST n) of
            Right x -> case (snd (applyOperarations ((test x), (State [] (Erros []))))) of
                              (State a (Erros [])) -> putStrLn "Ane compiles with sucesso\nAll definitions correct"
                              (State a (Erros x)) -> printState (State a (Erros x))
            Left x -> x