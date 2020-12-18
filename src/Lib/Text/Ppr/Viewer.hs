module Lib.Text.Ppr.Viewer where

import System.Console.Pretty

data Viewer
    = VEmpty
    | VText String
    | VStyle Style Viewer
    | VColor Color Viewer
    | VBeam
    | VVertical Viewer Viewer
    | VHorizontal Viewer Viewer
    | VField Int Int [String]
    deriving ()

mkVE :: Viewer
mkVE = VEmpty

mkVT :: String -> Viewer
mkVT ss1 = ss1 `seq` VText ss1

mkVS :: Style -> Viewer -> Viewer
mkVS s1 v1 = s1 `seq` v1 `seq` VStyle s1 v1

mkVC :: Color -> Viewer -> Viewer
mkVC c1 v1 = c1 `seq` v1 `seq` VColor c1 v1

mkVB :: Viewer
mkVB = VBeam

mkVV :: Viewer -> Viewer -> Viewer
mkVV v1 v2 = v1 `seq` v2 `seq` VVertical v1 v2

mkVH :: Viewer -> Viewer -> Viewer
mkVH v1 v2 = v1 `seq` v2 `seq` VHorizontal v1 v2

mkVF :: Int -> Int -> [String] -> Viewer
mkVF row1 col1 field1 = row1 `seq` col1 `seq` field1 `seq` VField row1 col1 field1

render :: Viewer -> String
render = unlines . linesFromVField . normalizeV where
    contract :: Viewer -> Viewer
    contract (VColor c1 v1) = contract v1
    contract (VStyle s1 v1) = contract v1
    contract v = v
    getMaxHeight :: [Viewer] -> Int
    getMaxHeight vs = maximum (0 : [ col | VField row col field <- map contract vs ])
    getMaxWidth :: [Viewer] -> Int
    getMaxWidth vs = maximum (0 : [ row | VField row col field <- map contract vs ])
    expandHeight :: Int -> Viewer -> Viewer
    expandHeight col VBeam = mkVF 1 col (replicate col "|")
    expandHeight col VEmpty = mkVF 0 col (replicate col "")
    expandHeight col (VStyle s1 v1) = mkVS s1 (expandHeight col v1)
    expandHeight col (VColor c1 v1) = mkVC c1 (expandHeight col v1)
    expandHeight col (VField row col' field) = mkVF row col (field ++ replicate (col - col') (replicate row ' '))
    expandWidth :: Int -> Viewer -> Viewer
    expandWidth row VBeam = mkVS Bold (mkVF row 1 [replicate row '-'])
    expandWidth row VEmpty = mkVF row 0 []
    expandWidth row (VStyle s1 v1) = mkVS s1 (expandWidth row v1)
    expandWidth row (VColor c1 v1) = mkVC c1 (expandWidth row v1)
    expandWidth row (VField row' col field) = mkVF row col [ str ++ replicate (row - row') ' ' | str <- field ]
    horizontal :: Viewer -> [Viewer]
    horizontal VBeam = return mkVB
    horizontal VEmpty = return mkVE
    horizontal (VField row col field) = return (mkVF row col field)
    horizontal (VColor c1 v1) = map (mkVC c1) (horizontal v1)
    horizontal (VStyle s1 v1) = map (mkVS s1) (horizontal v1)
    horizontal (VText ss1) = return (mkVF (length ss1) 1 [ss1])
    horizontal (VVertical v1 v2) = return (normalizeV (mkVV v1 v2))
    horizontal (VHorizontal v1 v2) = horizontal v1 ++ horizontal v2
    vertical :: Viewer -> [Viewer]
    vertical VBeam = return mkVB
    vertical VEmpty = return mkVE
    vertical (VField row col field) = return (mkVF row col field)
    vertical (VColor c1 v1) = map (mkVC c1) (vertical v1)
    vertical (VStyle s1 v1) = map (mkVS s1) (vertical v1)
    vertical (VText ss1) = return (mkVF (length ss1) 1 [ss1])
    vertical (VHorizontal v1 v2) = return (normalizeH (mkVH v1 v2))
    vertical (VVertical v1 v2) = vertical v1 ++ vertical v2
    reduce :: Viewer -> Viewer
    reduce (VColor c1 v1) = case reduce v1 of
        VField row1 col1 field1 -> mkVF row1 col1 (map (color c1) field1)
    reduce (VStyle s1 v1) = case reduce v1 of
        VField row1 col1 field1 -> mkVF row1 col1 (map (style s1) field1)
    reduce v1 = v1
    hsum :: Int -> [Viewer] -> Viewer
    hsum col [] = mkVF 0 col (replicate col "")
    hsum col (v : vs) = case (reduce v, hsum col vs) of
        (VField row1 _ field1, VField row2 _ field2) -> VField (row1 + row2) col (zipWith (++) field1 field2)
    vsum :: Int -> [Viewer] -> Viewer
    vsum row [] = mkVF row 0 []
    vsum row (v : vs) = case (reduce v, vsum row vs) of
        (VField _ col1 field1, VField _ col2 field2) -> VField row (col1 + col2) (field1 ++ field2)
    normalizeH :: Viewer -> Viewer
    normalizeH = merge . concat . map horizontal . flatten where
        flatten :: Viewer -> [Viewer]
        flatten (VHorizontal v1 v2) = flatten v1 ++ flatten v2
        flatten v1 = [v1]
        merge :: [Viewer] -> Viewer
        merge vs = hsum (getMaxHeight vs) (map (expandHeight (getMaxHeight vs)) vs)
    normalizeV :: Viewer -> Viewer
    normalizeV = merge . concat . map vertical . flatten where
        flatten :: Viewer -> [Viewer]
        flatten (VVertical v1 v2) = flatten v1 ++ flatten v2
        flatten v1 = [v1]
        merge :: [Viewer] -> Viewer
        merge vs = vsum (getMaxWidth vs) (map (expandWidth (getMaxWidth vs)) vs)
    linesFromVField :: Viewer -> [String]
    linesFromVField (VField row col field) = field
