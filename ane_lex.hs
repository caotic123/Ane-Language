module AneLexer where

{-# LANGUAGE FlexibleContexts #-}
import Data.Char

data Lexical_Erros = Lexical_Erros Char deriving Show
data Lexical_Structure = Lexical_Structure (String, (Int, Int)) (Maybe [Lexical_Erros]) deriving Show
data Token = String (Int, Int)
data Lex = Lex [Token]

basic_symbols = ['.', '\\', '-', '>', '*', ':', '_', '\n', '=', '(', ')', '[', ']']
lex_s = [isAlpha, \x -> elem x basic_symbols]

concat_lex_erros x y = case x of 
                         Just d -> Just (y : d)
                         Nothing -> x

check_lex :: Maybe [Lexical_Erros] -> Char -> Maybe [Lexical_Erros]
check_lex p k = if (not (foldl1 (\x -> \y -> x || y) (map (\x -> x k) lex_s))) then 
    Just ((Lexical_Erros k) : (case p of
                                     Just p -> p
                                     Nothing -> []))
                  else p

walk :: Lexical_Structure -> Lexical_Structure
walk (Lexical_Structure ("", (k, y)) n) = (Lexical_Structure ("", (k, y)) n)
walk (Lexical_Structure (t, (k, y)) n) = if ((ac == ' ') || ac == '.') then (Lexical_Structure ("", (k+1, y)) n) else concat_lex (walk (Lexical_Structure (tail t, (k, y)) n)) ac
     where concat_lex (Lexical_Structure (t_, (k_, y_)) n_) y = (Lexical_Structure (if y == '\n' then t_ else y : t_ , cur) (check_lex n_ y))
                                                                  where 
                                                                    cur = (k_+1, y_ + (if y == '\n' then 1 else 0))
           ac = (head t)

lexer :: ([Lexical_Structure], (String, (Int, Int))) -> ([Lexical_Structure], (String, (Int, Int))) -- ([Lex structures builded], (what need by consumed by lexer, position of consumed words))
lexer (y, (k, (x, x_))) = if ((length str) == 0) then (y, ("", (x, x_))) else (lexer ((y ++ [lex_d]), (k, (continuation_consumed lex_d))))
  where
    str = (drop x k)
    lex_d = (walk (Lexical_Structure (str, (x, x_)) Nothing))
    continuation_consumed (Lexical_Structure (t, (k, y)) n) = (k, y)

correctLex :: [Lexical_Structure]-> Maybe ([(Int, Int)], [[Lexical_Erros]])
correctLex [] = Nothing
correctLex (k : xs) = case k of
                      Lexical_Structure (t, (k, y)) Nothing -> correctLex xs
                      Lexical_Structure (t, (k, y)) (Just d) -> 
                        (\x -> \yy -> case x of
                                        Just (x_,  x) -> Just ((k, y) : x_, (yy : x))
                                        Nothing -> Just ([(k, y)], [yy])
                           ) (correctLex xs) d

getLex str = (lexer ([], (str, (0, 1))))

safe_head :: [a] -> Maybe a
safe_head xs = case xs of
                 (x : xs_) -> Just x
                 _ -> Nothing

safe_fold1_f :: (a -> a -> a) -> [a] -> Maybe a
safe_fold1_f _ [] = Nothing
safe_fold1_f f xs = Just (foldl1 f xs)

lex_col :: (Int, Int) -> [Lexical_Structure] -> Maybe Int
lex_col (k, k_) d = case (safe_fold1_f f_ (filter (\y -> case y of
                      Lexical_Structure (p, (x, y_)) n -> k_ == y_) d)) of
                       Just (Lexical_Structure (p_, (x_, y_)) n) -> Just x_
                       Nothing -> Nothing
  where f_ (Lexical_Structure (p_, (x_, y_)) n_) (Lexical_Structure (p__, (x__, y__)) n__) = if x_ < x__ then Lexical_Structure (p_, (x_, y_)) n_ else Lexical_Structure (p__, (x__, y__)) n__

print_lex_erros :: [Lexical_Structure] -> ([(Int, Int)], [[Lexical_Erros]]) -> IO ()
print_lex_erros t (_, []) = return ()
print_lex_erros t ((x, y_) : xs__, (y : xs)) = pr (x, y_) y >> print_lex_erros t (xs__, xs)
  where pr (x, y_) ((Lexical_Erros p) : ys) = do
                                           let col = (case (lex_col (x, y_) t) of
                                                        Just a -> show (x - a) :: String
                                                        Nothing -> "?")
                              
                                           putStrLn "Lexical Error"
                                           putStrLn ("Line " ++ (show y_ :: String) ++ " Col Starting " ++ col :: String)
                                           putStrLn ("In " ++ [p])
                                           pr (x, y_) ys
        pr _ [] = return ()
                 

lex_ :: String -> Either (IO ()) ([Lexical_Structure], (String, (Int, Int)))
lex_ k = case (correctLex (getLexMaybeErros lex)) of
           Nothing -> Right lex
           Just x -> Left (print_lex_erros (getStructLex lex) x)
  where lex = (getLex k)
        getLexMaybeErros (n, (t, (x, y))) = n
        getStructLex (n, (t, x)) = n

get_lex t = case (lex_ t) of
              Right x -> Right t
              Left x -> Left x
