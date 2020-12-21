module Lib.Base where

import Control.Applicative
import Control.Monad

type Precedence = Int

type Indentation = Int

newtype PM output
    = PM { runPM :: String -> [(output, String)] }
    deriving ()

class Outputable a where
    pprint :: Precedence -> a -> String -> String

instance Functor PM where
    fmap a2b fa = PM $ \str -> [ (a2b a, str') | (a, str') <- fa `runPM` str ]
    a <$ fb = PM $ \str -> [ (a, str') | (b, str') <- fb `runPM` str ]

instance Applicative PM where
    pure a = PM $ \str -> [(a, str)]
    fa2b <*> fa = PM $ \str -> [ (a2b a, str'') | (a2b, str') <- fa2b `runPM` str, (a, str'') <- fa `runPM` str' ]
    fa *> fb = PM $ \str -> [ (b, str'') | (a, str') <- fa `runPM` str, (b, str'') <- fb `runPM` str' ]
    fa <* fb = PM $ \str -> [ (a, str'') | (a, str') <- fa `runPM` str, (b, str'') <- fb `runPM` str' ]

instance Alternative PM where
    empty = PM $ \str -> []
    fa <|> fa' = PM $ \str -> fa `runPM` str ++ fa' `runPM` str
    many fa = PM $ \str -> some fa `runPM` str ++ [([], str)]
    some fa = PM $ \str -> [ (a : as, str'') | (a, str') <- fa `runPM` str, (as, str'') <- many fa `runPM` str' ]

instance Monad PM where
    return = PM . curry return
    ma >>= a2mb = PM (flip (>>=) (uncurry (runPM . a2mb)) . runPM ma)
    (>>) = (*>)

instance MonadPlus PM where
    mzero = PM (pure mzero)
    mplus ma ma' = PM (pure mplus <*> runPM ma <*> runPM ma')

instance MonadFail PM where
    fail = PM . const . fail

instance Semigroup (PM a) where
    p1 <> p2 = p1 <|> p2

instance Monoid (PM a) where
    mempty = empty

autoPM :: Read a => Precedence -> PM a
autoPM = PM . readsPrec

acceptCharIf :: (Char -> Bool) -> PM Char
acceptCharIf condition = PM go where
    go :: String -> [(Char, String)]
    go (ch : str)
        | condition ch = return (ch, str)
    go _ = []

consumeStr :: String -> PM ()
consumeStr prefix = PM $ \str -> let n = length prefix in if take n str == prefix then return ((), drop n str) else []

matchPrefix :: String -> PM ()
matchPrefix prefix = PM $ \str -> let n = length prefix in if take n str == prefix then return ((), str) else []

strstr :: String -> String -> String
strstr str1 str2 = str1 ++ str2

strcat :: [String -> String] -> String -> String
strcat = foldr (.) id

nl :: String -> String
nl str = "\n" ++ str

pindent :: Indentation -> String -> String
pindent space str1 = if space < 0 then str1 else replicate space ' ' ++ str1

ppunc :: String -> [String -> String] -> String -> String
ppunc str [] = id
ppunc str (delta : deltas) = delta . foldr (\delta0 -> \acc -> strstr str . delta0 . acc) id deltas

plist :: Indentation -> [String -> String] -> String -> String
plist space [] = strstr "[]"
plist space (delta : deltas) = nl . pindent space . strstr "[ " . loop delta deltas where
    loop :: (String -> String) -> [String -> String] -> String -> String
    loop delta1 [] = delta1 . nl . pindent space . strstr "]"
    loop delta1 (delta2 : deltas) = delta1 . nl . pindent space . strstr ", " . loop delta2 deltas

split' :: (a -> a -> Bool) -> [a] -> [[a]]
split' cond [] = []
split' cond (x1 : x2 : xs)
    | cond x1 x2 = case split' cond (x2 : xs) of
        y : ys -> (x1 : y) : ys
split' cond (x1 : xs) = [x1] : split' cond xs

printPretty :: Outputable a => a -> String
printPretty = flip (pprint 0) ""
