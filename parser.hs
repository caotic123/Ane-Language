module AneParser where

import AneLexer
import Text.Parsec
import Data.HashMap

data VarUnit = I | X VarUnit deriving (Show, Eq, Ord)
data TermOrLambda = VarTerm String | VarLambda Lambda deriving Show

data Lambda = Lambda TermBody deriving (Show, Eq)
data Var = VarName String | VarCode VarUnit deriving (Show, Eq, Ord)
data TermBody = FreeVar Var | LambdaTerm Lam | App TermBody TermBody deriving (Show, Eq)
data Lam = Lam Var TermBody deriving (Show, Eq)

data Finish = Finish TermOrLambda | MFinish [(TermOrLambda, TermOrLambda)] deriving Show
data Operations = CheckFinish Finish 
                 | Apply String 
                 | ApplyTerms String
                 | BetaReduction (String, String, TermOrLambda)
                 | BetaExpasion (String, String, TermOrLambda) 
                 | Recursion (String, String, TermOrLambda) 
                 | Equal (String, String)
                 | CheckType (String, TypeLambda)
                 | NoHasSideVar String
                 | Normalization (String, TypeLambda)
                 | Show deriving Show

data Type = Type deriving (Show, Eq, Ord)
data TypeLambda = TypeLambda TypeLambda TypeLambda | SingleType Type | Undefined | Test deriving (Show, Eq, Ord)
data TypedTermBody = TypedFreeVar Var TypeLambda | TypedLambdaTerm TypedLam TypeLambda | TypedApp TypedTermBody TypedTermBody TypeLambda deriving (Show, Eq, Ord)
data TypedLam = TypedLam Var TypedTermBody deriving (Show, Eq, Ord)

type Term = Map String Lambda
data Definition = Definition String Term [Operations] deriving Show
data AST = AST [Definition] deriving Show

point :: Parsec String st a -> Parsec String st Char
point k = k >> (char '.')

with_spaces :: Parsec String st a -> Parsec String st ()
with_spaces k = (spaces) >> k >> (spaces)

consumeDefinitionName :: Parsec String st Definition
consumeDefinitionName = ((many letter) >>= (\x -> return (Definition x empty [])))

consumeDefinitionHead = (string "Definition") >> (spaces) >> (char ':') >> (spaces)

endTerms = (with_spaces (point (string "End_Terms")))

insertTupleInMap (Definition xs d p) ((k, x) : ys) = insertTupleInMap (Definition xs (insert k x d) p) ys
insertTupleInMap (Definition xs d p) [] = (Definition xs d p)

consumeComplexFinish :: Finish-> Parsec String st Finish
consumeComplexFinish (MFinish xs) = between (char '[') (char ']') fx
 where fx = do
         f <- tryConsumesLambdaOrTerm
         (with_spaces (char ':'))
         c <- tryConsumesLambdaOrTerm
         return (MFinish ((f, c) : xs))

singleFinish :: Parsec String st Finish
singleFinish = do
                   f <- tryConsumesLambdaOrTerm
                   return (Finish f)

consumeFinish :: Parsec String st Operations
consumeFinish = do
                 (with_spaces (string "Finish as"))
                 d <- try getManyComplexFinish   <|> singleFinish
                 return (CheckFinish d)
  where
      f_ (MFinish x) = x
      complex_finish___ = do 
            f <- (consumeComplexFinish (MFinish [])) 
            (spaces)
            return f
      getManyComplexFinish = (many complex_finish___) >>= (\x -> return (foldl1 (\x -> \y -> MFinish ((f_ x) ++ (f_ y))) x))


consumesOperationWithOneArgument ::  String -> Parsec String st String
consumesOperationWithOneArgument k = do
                                      (string k)
                                      (space)
                                      (with_spaces (return ()))
                                      (many letter)

consumesApply :: Parsec String st Operations
consumesApply = consumesOperationWithOneArgument "Apply" >>= (\x -> return (Apply x))

consumesApplyTerms :: Parsec String st Operations
consumesApplyTerms= consumesOperationWithOneArgument "Apply-Terms" >>= (\x -> return (ApplyTerms x))

consumesHasSideVar :: Parsec String st Operations
consumesHasSideVar = consumesOperationWithOneArgument "Reducible" >>= (\x -> return (NoHasSideVar x))

consumesTypeNotation :: Parsec String st TypeLambda
consumesTypeNotation = between (char '(') (char ')') fx
  where fx = do
              k <- try consumesTypeNotation <|> ((char '*') >>= (\_ -> return (SingleType Type)))
              (with_spaces (return ()))
              (string "->")
              (with_spaces (return ()))
              e <- try consumesTypeNotation <|> ((char '*') >>= (\_ -> return (SingleType Type)))
              return (TypeLambda k e)

consumesTypeChecker :: Parsec String st Operations
consumesTypeChecker = do
                    (string "Type of") 
                    (space)
                    (with_spaces (return ()))
                    t <- many letter
                    (space)
                    (string "is")
                    (space)
                    (with_spaces (return ()))
                    t_ <- consumesTypeNotation
                    return (CheckType (t, t_))

consumesNormalization :: Parsec String st Operations
consumesNormalization = do
                    (string "Normalization of") 
                    (space)
                    (with_spaces (return ()))
                    t <- many letter
                    (space)
                    (string "strongly by")
                    (space)
                    (with_spaces (return ()))
                    t_ <- consumesTypeNotation
                    return (Normalization (t, t_))

consumesEquality :: Parsec String st Operations
consumesEquality = do
                   (string "Equal")
                   (space)
                   (with_spaces (return ()))
                   t <- many letter
                   (space)
                   (string "and")
                   (space)
                   (with_spaces (return ()))
                   t_ <- many letter
                   return (Equal (t, t_))

tryConsumesLambdaOrTerm :: Parsec String st TermOrLambda
tryConsumesLambdaOrTerm = try (parseLambda >>= (\x -> return (VarLambda x))) <|> ((many letter) >>= (\x -> return (VarTerm x)))

consumesBetaOperations :: String -> Parsec String st (String, String, TermOrLambda)
consumesBetaOperations bk__ = do
                            let in_ = (with_spaces (string "in"))
                            (string bk__)
                            (space)
                            (with_spaces (return ()))
                            k <- many letter
                            in_
                            t <- many letter
                            in_
                            c <- tryConsumesLambdaOrTerm   
                            return (k, t, c)  
               
consumesBetaReduction :: Parsec String st Operations
consumesBetaReduction = (consumesBetaOperations "Beta-Reduction") >>= (\t -> return (BetaReduction t))

consumesExpasionReduction :: Parsec String st Operations
consumesExpasionReduction = (consumesBetaOperations "Beta-Expasion") >>= (\t -> return (BetaExpasion t))

consumesRecursiveApply:: Parsec String st Operations
consumesRecursiveApply = (consumesBetaOperations "Recursive-Apply") >>= (\t -> return (Recursion t))

getOps :: Parsec String st Operations
getOps = do
           f <- choice [try consumeFinish, try consumesApply, try consumesRecursiveApply, try consumesBetaReduction, try consumesEquality, try consumesHasSideVar, try consumesApplyTerms, try consumesTypeChecker, try consumesNormalization, (string "Show") >> (return Show)]
           (with_spaces (point (return ())))
           return f

insert_op [] (Definition q w e) = (Definition q w e) 
insert_op ys (Definition q w []) = (Definition q w ys)
insert_op (x : xs) (Definition d u ys) = insert_op (tail ys) (Definition d u (x : ys))

buildDefinitionAST :: AST -> Parsec String st AST
buildDefinitionAST (AST xs) = do
                       let getMapTerm (Definition _ x _) = x
                       consumeDefinitionHead
                       f <- consumeDefinitionName
                       (with_spaces (point (return ())))
                       d <- many (try getTerm)
                       endTerms
                       c <- many (try getOps)
                       return (AST ((insert_op c (insertTupleInMap f d)) : xs))

end_DefinitionAST :: AST -> Parsec String st AST
end_DefinitionAST(AST xs) = (with_spaces (point (string "End_Definition"))) >> return (AST xs)

freeVariableConsumes :: Parsec String st Var
freeVariableConsumes = do 
                         f <- many (try letter <|> oneOf "*")
                         return (VarName f)

catch_free_var_as_TermBody = freeVariableConsumes >>= (\x -> return (FreeVar x))
catch_lambda_as_Termoby = consumesLambda >>= (\y -> return (LambdaTerm y))

consumesAplication :: Parsec String st TermBody
consumesAplication = (between (char '(') (char ')') fapp)
   where fapp = do
                ((try consumesAplication <|> consumesAppTerms) >>= (\x -> (space >> spaces >> (try consumesAplication <|> consumesAppTerms)) >>= (\y -> return (App x y))))
         consumesAppTerms = (try catch_lambda_as_Termoby <|> catch_free_var_as_TermBody)
         tapp k = return (foldl1 (\x -> \y -> App x y) k)

consumesLambda :: Parsec String st Lam
consumesLambda = (try fx) <|> (between (char '(') (char ')') fx)
  where fx = do 
               (with_spaces (char 'λ'))
               fname <- many letter
               (with_spaces (string "->"))
               f <- (try catch_lambda_as_Termoby) <|> (try (consumesAplication)) <|> catch_free_var_as_TermBody
               return (Lam (VarName fname) f)
 
parseLambda :: Parsec String st Lambda
parseLambda = do
                t <- consumesLambda
                return (Lambda (LambdaTerm t))

getTerm :: Parsec String st (String, Lambda)
getTerm = do 
             (with_spaces (string "Term"))
             d <- many letter
             (spaces)
             (with_spaces (char ':'))
             parseLambda >>= (\y -> (point (return ())) >>= (\_ -> return (d, y)))

getDefinition :: AST -> [Definition]
getDefinition (AST y) = y

concatDefinitions [] = AST []
concatDefinitions ((AST y) : xs) = (AST (y ++ getDefinition (concatDefinitions xs))) 

parsebydefinition :: AST -> Parsec String st AST
parsebydefinition (AST xs) = do
                      d <- buildDefinitionAST (AST xs)
                      t <- (end_DefinitionAST (AST xs))
                      c <- many (parsebydefinition (AST xs))
                      return (AST ((getDefinition d) ++ (getDefinition t) ++ (getDefinition (concatDefinitions c))))

getAneAST :: String -> Either (IO ()) AST
getAneAST n = case (get_lex n) of
                Right x -> do
                             case (parse (parsebydefinition (AST [])) "" n) of
                                Right x_ -> Right x_
                                Left y_ -> Left (print y_)
                Left y-> Left y