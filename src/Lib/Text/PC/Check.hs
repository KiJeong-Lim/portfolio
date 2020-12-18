module Lib.Text.PC.Check where

import Lib.Text.PC.Base
import Test.QuickCheck
import Test.QuickCheck.Checkers

instance (Arbitrary err, Arbitrary chr, CoArbitrary chr, Show chr, Arbitrary val) => Arbitrary (ParserBase err chr val) where
    arbitrary = elements [0, 1 .. 5] >>= foldNat base step where
        base :: (Arbitrary err, Arbitrary chr, CoArbitrary chr, Show chr, Arbitrary val) => Gen (ParserBase err chr val)
        base = do
            val1 <- arbitrary
            return (PVal val1)
        step :: (Arbitrary err, Arbitrary chr, CoArbitrary chr, Show chr, Arbitrary val) => Int -> Gen (ParserBase err chr val) -> Gen (ParserBase err chr val)
        step n prev = oneof
            [ do
                err1 <- arbitrary
                alts1 <- vectorOf n ((,) <$> prev <*> arbitrary)
                return (PAlt err1 alts1)
            , do
                act1 <- liftArbitrary prev
                return (PAct act1)
            ]

instance (Eq err, Eq chr, Arbitrary chr, Show chr, Eq val) => EqProp (ParserBase err chr val) where
    PVal val1 =-= PVal val2 = property (val1 == val2)
    PAlt err1 alts1 =-= PAlt err2 alts2 = property (err1 == err2 && length alts1 == length alts2) .&&. conjoin [ p1 =-= p2 .&&. property (str1 == str2) | ((p1, str1), (p2, str2)) <- zip alts1 alts2  ]
    PAct act1 =-= PAct act2 = act1 =-= act2
    _ =-= _ = property False

foldNat :: a -> (Int -> a -> a) -> Int -> a
foldNat base step n
    | n < 0 = error "foldNat: negative argument"
    | n == 0 = base
    | otherwise = step (n - 1) (foldNat base step (n - 1))
