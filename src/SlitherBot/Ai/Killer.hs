{-# LANGUAGE BangPatterns    #-}
{-# LANGUAGE RecordWildCards #-}
module SlitherBot.Ai.Killer
    ( KillerAiState
    , killerAi
    ) where

import           Control.Monad        (guard)
import           Data.Fixed           (mod')
import qualified Data.Foldable        as Foldable
import qualified Data.HashMap.Strict  as HMS
import           Data.List            (maximumBy)
import           Data.Maybe           (mapMaybe, maybeToList)
import           Data.Ord             (Down (..), comparing)
import qualified Data.Sequence        as Seq
import           Debug.Trace          (trace)
import qualified Linear.Metric        as Linear
import           Linear.V2
import           SlitherBot.Ai
import           SlitherBot.GameState
import           SlitherBot.Protocol

--------------------------------------------------------------------------------

newtype Radians = Radians {unRadians :: Double} deriving (Eq, Ord)

instance Show Radians where show (Radians x) = show x

clampRadians :: Double -> Double
clampRadians r0 =
    let r1 = r0 `mod'` (2 * pi) in
    if r1 > pi then r1 - 2 * pi else r1

instance Num Radians where
    (Radians x) + (Radians y) = Radians (clampRadians $! x + y)
    (Radians x) - (Radians y) = Radians (clampRadians $! x - y)
    (Radians x) * (Radians y) = Radians (clampRadians $! x * y)

    abs    (Radians x) = Radians (abs x)
    signum (Radians x) = Radians (signum x)

    fromInteger             = mkRadians . fromIntegral

mkRadians :: Double -> Radians
mkRadians = Radians . clampRadians

--------------------------------------------------------------------------------

data KillerAiState = KillerAiState

data DirSnake = DirSnake
    { dsHead :: !(V2 Double)
    , dsDir  :: !Radians
    } deriving (Show)

lookAheadDistance :: Double
lookAheadDistance = 1000

enemyLookAhead :: Double
enemyLookAhead = 100

maxTurnAngle :: Double
maxTurnAngle = pi / 4

foodRadius :: Double
foodRadius = 400

killerBeamLength :: Double
killerBeamLength = 1000

data TurnStrategy
    = PlainTurn {tsRelativeTurn :: !Radians}
    | FoodTurn  {tsRelativeTurn :: !Radians, tsFood :: !Double}
    deriving (Eq, Show)

instance Ord TurnStrategy where
    compare (FoodTurn _ x) (FoodTurn _ y) = compare x y
    compare (PlainTurn _)  (FoodTurn _ _) = LT
    compare (FoodTurn _ _) (PlainTurn _)  = GT
    compare (PlainTurn x)  (PlainTurn y)  =
        -- Prefer going straight?  This is broken with the Radians type.
        compare (Down $ abs x) (Down $ abs y)

normalTurns :: [TurnStrategy]
normalTurns = map PlainTurn $
    turns ++ map negate turns ++ [0]
  where
    numTurns = 3 :: Int
    turns    =
        [ mkRadians $ fromIntegral ix * (maxTurnAngle / fromIntegral numTurns)
        | ix <- [1 .. numTurns]
        ]

foodTurns :: DirSnake -> GameState -> [TurnStrategy]
foodTurns DirSnake {..} GameState {..} = do
    (foodPos, food) <- HMS.toList gsFoods
    guard $ Linear.distance dsHead foodPos < foodRadius
    let turn                = toAngle (foodPos - dsHead)
        relTurn@(Radians r) = turn - dsDir
    guard $ -maxTurnAngle <= r && r <= maxTurnAngle
    return $ FoodTurn {tsRelativeTurn = relTurn, tsFood = foodValue food}

data LineSegment = LineSegment !(V2 Double) !(V2 Double)
    deriving (Show)

data Box = Box !(V2 Double) !(V2 Double)
    deriving (Show)

lineSegmentToBox :: LineSegment -> Box
lineSegmentToBox (LineSegment (V2 x1 y1) (V2 x2 y2)) =
    Box (V2 (min x1 x2) (min y1 y2)) (V2 (max x1 x2) (max y1 y2))
{-# INLINE lineSegmentToBox #-}

boxIntersection :: Box -> Box -> Bool
boxIntersection
        (Box (V2 left1 top1) (V2 right1 bottom1))
        (Box (V2 left2 top2) (V2 right2 bottom2)) = not $
    left1   > right2  ||
    top1    > bottom2 ||
    right1  < left2   ||
    bottom1 < top2
{-# INLINE boxIntersection #-}

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

toAngle :: V2 Double -> Radians
toAngle (V2 x y) = mkRadians $ atan2 y x
{-# INLINE toAngle #-}

fromAngle :: Radians -> V2 Double
fromAngle (Radians r) = angle r
{-# INLINE fromAngle #-}

updateKillerAi :: Snake -> GameState -> (AiOutput, KillerAiState)
updateKillerAi ownSnake gs@GameState{..} = case makeDirSnake ownSnake of
    Nothing                      -> (AiOutput 0 False, KillerAiState)
    Just ds@(DirSnake _head_ dir) ->
        let nextSegments =
                [ (turn, evaluateStrategy turn ds)
                | turn <- normalTurns ++ foodTurns ds gs
                ] in

        case nextSegments of
            [] -> (AiOutput 0 False, KillerAiState)
            _  ->
                let (ts, _)   = maximumBy (comparing snd) nextSegments
                    bestAngle = dir + tsRelativeTurn ts in
                (AiOutput (unRadians bestAngle) False, KillerAiState)
  where
    dist = lookAheadDistance

    otherSnakes =
        [ snake
        | (snakeId, snake) <- HMS.toList gsSnakes
        , Just snakeId /= gsOwnSnake
        ]

    otherDirSnakes         = mapMaybe makeDirSnake otherSnakes
    otherSnakeLineSegments = concatMap snakeLineSegments otherSnakes

    snakeLineSegments snake =
        maybeToList (snakeLookAhead enemyLookAhead <$> makeDirSnake snake) ++
        snakeBodyToLineSegments (snakeBody snake)

    evaluateStrategy
        :: TurnStrategy -> DirSnake -> Double
    evaluateStrategy ts ds@DirSnake {..} =
        let turn    = dsDir + tsRelativeTurn ts
            segment = LineSegment dsHead (dsHead + (fromAngle turn .* dist))
            avoid   = closestIntersection segment otherSnakeLineSegments
            killer  = killerBeamScores ds otherDirSnakes in
        sumScores ts killer avoid

makeDirSnake :: Snake -> Maybe DirSnake
makeDirSnake snake = case Seq.viewl (snakeBody snake) of
    Seq.EmptyL         -> Nothing
    head_ Seq.:< body1 -> case Seq.viewl body1 of
        Seq.EmptyL    -> Nothing
        neck Seq.:< _ ->
            let !dir = toAngle (head_ - neck) in
            Just $! DirSnake head_ dir

snakeLookAhead :: Double -> DirSnake -> LineSegment
snakeLookAhead dist (DirSnake head_ dir) =
    let offset = fromAngle dir .* dist in
    LineSegment head_ (head_ + offset)

data AvoidScore
    = AvoidedScore
    | NotAvoidedScore !Double
    deriving (Eq, Show)

closestIntersection :: LineSegment -> [LineSegment] -> AvoidScore
closestIntersection travel@(LineSegment head_ _) =
    go AvoidedScore
  where
    travelBox = lineSegmentToBox travel

    quickIntersection segment =
        if boxIntersection travelBox (lineSegmentToBox segment)
            then lineSegmentIntersection travel segment
            else NonIntersecting

    go acc [] = acc
    go acc (segment : segments) = case quickIntersection segment of
        NonIntersecting -> go acc segments
        Parallel        -> go acc segments
        Colinear        -> go acc segments
        Intersecting x  -> case acc of
            AvoidedScore ->
                go (NotAvoidedScore $ Linear.distance head_ x) segments
            NotAvoidedScore dist ->
                go (NotAvoidedScore $ min dist (Linear.distance head_ x))
                    segments

newtype KillerBeamScore = KillerBeamScore {unKillerBeamScore :: Double}
    deriving (Show)

killerBeamScore :: DirSnake -> DirSnake -> KillerBeamScore
killerBeamScore ourSnake theirSnake =
    let ourHead   = dsHead ourSnake
        theirHead = dsHead theirSnake
        ourTgt    = ourHead   + fromAngle (dsDir ourSnake)   .* kbl
        theirTgt  = theirHead + fromAngle (dsDir theirSnake) .* kbl
        ourBeam   = LineSegment ourHead   ourTgt
        theirBeam = LineSegment theirHead theirTgt in
    case lineSegmentIntersection ourBeam theirBeam of
        Intersecting point -> KillerBeamScore $!
            let score = Linear.distance theirHead point -
                        Linear.distance ourHead point

                -- Lower points matter more!
                penaltyFactor = if score < 0 then 2 else 1

                -- Closer snakes matter more!
                closeFactor = (100 / Linear.distance theirHead ourHead) in

            score * penaltyFactor * closeFactor

        _ -> KillerBeamScore 0
  where
    kbl = killerBeamLength

killerBeamScores :: DirSnake -> [DirSnake] -> KillerBeamScore
killerBeamScores ourSnake =
    KillerBeamScore . sum . map (unKillerBeamScore . killerBeamScore ourSnake)

sumScores
    :: TurnStrategy
    -> KillerBeamScore
    -> AvoidScore
    -> Double
sumScores turnStategy killerBeam avoid =
    let total = turnStrategyScore + killerBeamScore + avoidScore in
    trace (show total ++
        " (" ++ show (tsRelativeTurn turnStategy) ++
        " turn: " ++ show turnStrategyScore ++
        ", killer: " ++ show killerBeamScore ++
        ", avoid: " ++ show avoidScore ++ ")") $
        total
  where
    turnStrategyScore = case turnStategy of
        PlainTurn _   -> 0
        FoodTurn  _ v -> v  -- Food value, 1 to 50

    killerBeamScore = case killerBeam of
        KillerBeamScore v -> v

    avoidScore = case avoid of
        AvoidedScore         -> 0
        NotAvoidedScore dist -> -dist * 10
