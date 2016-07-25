{-# LANGUAGE BangPatterns    #-}
{-# LANGUAGE RecordWildCards #-}
module SlitherBot.Ai.Killer
    ( KillerAiState
    , killerAi
    ) where

import qualified Data.Foldable        as Foldable
import qualified Data.HashMap.Strict  as HMS
import           Data.List            (maximumBy)
import           Data.Maybe           (maybeToList)
import           Data.Ord             (comparing)
import qualified Data.Sequence        as Seq
import qualified Linear.Metric        as Linear
import           Linear.V2
import           SlitherBot.Ai
import           SlitherBot.GameState

data KillerAiState = KillerAiState

lookAheadDistance :: Double
lookAheadDistance = 400

possibleTurns :: [Double]
possibleTurns =
    turns ++ map negate turns ++ [0]
  where
    maxTurn  = pi / 2
    numTurns = 3 :: Int
    turns    =
        [ fromIntegral ix * (maxTurn / fromIntegral numTurns)
        | ix <- [1 .. numTurns]
        ]

data LineSegment = LineSegment !(V2 Double) !(V2 Double)
    deriving (Show)

data Box = Box !(V2 Double) !(V2 Double)
    deriving (Show)

lineSegmentToBox :: LineSegment -> Box
lineSegmentToBox (LineSegment (V2 x1 y1) (V2 x2 y2)) =
    Box (V2 (min x1 x2) (min y1 y2)) (V2 (max x1 x2) (max y1 y2))

(./) :: V2 Double -> Double -> V2 Double
(V2 x y) ./ s = V2 (x / s) (y / s)
{-# INLINE (./) #-}
infixl 7 ./

(.*) :: V2 Double -> Double -> V2 Double
(V2 x y) .* s = V2 (x * s) (y * s)
{-# INLINE (.*) #-}
infixl 7 .*

data LineSegmentIntersection
    = Colinear
    | Parallel
    | NonIntersecting
    | Intersecting !(V2 Double)
    deriving (Show)

lineSegmentIntersection :: LineSegment -> LineSegment -> LineSegmentIntersection
lineSegmentIntersection (LineSegment start1 end1) (LineSegment start2 end2)
    | rCrossS == 0 && qMinusPCrossR == 0 = Colinear
    | rCrossS == 0 && qMinusPCrossR /= 0 = Parallel
    | rCrossS /= 0 && 0 <= t && t <= 1 && 0 <= u && u <= 1 =
        Intersecting $! p + r .* t
    | otherwise = NonIntersecting
  where
    !p = start1
    !r = end1 - start1
    !q = start2
    !s = end2 - start2

    !qMinusP = q - p
    !t       = qMinusP `crossZ` (s ./ (r `crossZ` s))
    !u       = qMinusP `crossZ` (r ./ (r `crossZ` s))

    !rCrossS       = r `crossZ` s
    !qMinusPCrossR = qMinusP `crossZ` s

snakeBodyToLineSegments :: SnakeBody -> [LineSegment]
snakeBodyToLineSegments snakeBody =
    [ LineSegment l r
    | (l, r) <- paired (Foldable.toList snakeBody)
    ]
  where
    paired ls = zip (drop 1 ls) ls

killerAi :: Ai KillerAiState
killerAi = Ai
    { aiInitialState = KillerAiState
    , aiUpdate = \gs@GameState{..} _ -> case gsOwnSnake of
        Nothing ->
            (AiOutput 0 False, KillerAiState)
        Just ourSnakeId -> case HMS.lookup ourSnakeId gsSnakes of
            Nothing -> error $ "Could not find our snake " ++ show ourSnakeId
            Just snake -> updateKillerAi snake gs
    , aiHtmlStatus = mempty
    }

toAngle :: V2 Double -> Double
toAngle (V2 x y) = atan2 y x
{-# INLINE toAngle #-}

updateKillerAi :: Snake -> GameState -> (AiOutput, KillerAiState)
updateKillerAi ownSnake GameState{..} = case snakeNeck ownSnake of
    Nothing                       -> (AiOutput 0 False, KillerAiState)
    Just (Neck (LineSegment neck head_)) ->
        let direction    = toAngle (head_ - neck)
            nextSegments =
                [ LineSegment head_ (head_ + (angle (direction + turn) .* dist))
                | turn <- possibleTurns
                ]
            withScores   =
                [ (segment, closestIntersection segment otherSnakeLineSegments)
                | segment <- nextSegments
                ] in

        case withScores of
            [] -> (AiOutput 0 False, KillerAiState)
            _  ->
                let best = maximumBy (comparing snd) withScores
                    LineSegment start end = fst best
                    bestAngle = toAngle (end - start) in
                (AiOutput bestAngle False, KillerAiState)
  where
    dist = lookAheadDistance

    otherSnakes =
        [ snake
        | (snakeId, snake) <- HMS.toList gsSnakes
        , Just snakeId /= gsOwnSnake
        ]

    otherSnakeLineSegments = concatMap snakeLineSegments otherSnakes

    snakeLineSegments snake =
        maybeToList (neckLookAhead dist <$> snakeNeck snake) ++
        snakeBodyToLineSegments (snakeBody snake)

newtype Neck = Neck LineSegment

snakeNeck :: Snake -> Maybe Neck
snakeNeck snake = case Seq.viewl (snakeBody snake) of
    Seq.EmptyL         -> Nothing
    head_ Seq.:< body1 -> case Seq.viewl body1 of
        Seq.EmptyL    -> Nothing
        neck Seq.:< _ -> Just (Neck (LineSegment neck head_))

neckLookAhead :: Double -> Neck -> LineSegment
neckLookAhead dist (Neck (LineSegment n h)) =
    let offset = angle (toAngle $ h - n) .* dist in
    LineSegment h (h + offset)

closestIntersection :: LineSegment -> [LineSegment] -> Score
closestIntersection travel@(LineSegment head_ _) =
    go NonIntersectingScore
  where
    go acc [] = acc
    go acc (segment : segments) = case lineSegmentIntersection travel segment of
        NonIntersecting -> go acc segments
        Parallel        -> go acc segments
        Colinear        -> go acc segments
        Intersecting x  ->
            go (min acc (IntersectingScore $ Linear.distance head_ x)) segments

data Score
    = NonIntersectingScore
    | IntersectingScore !Double
    deriving (Eq, Show)

instance Ord Score where
    compare NonIntersectingScore  NonIntersectingScore  = EQ
    compare NonIntersectingScore  _                     = GT
    compare _                     NonIntersectingScore  = LT
    compare (IntersectingScore x) (IntersectingScore y) = compare x y
