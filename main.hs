import Data.Maybe
import Data.List
import Data.Char
import Control.Applicative
import Data.Map (Map)
import Debug.Trace
import Data.Set (Set)
import System.Environment
import qualified Data.Map as Map
import qualified Data.Set as Set

-- Regex over (∑∪ε)xN, epsilon is '\0'
data Regex  = Primitive Char Int
            | RSum Regex Regex
            | RMul Regex Regex
            | Kleene Regex
            deriving (Show)

--                       State             [(NextState, Add)]
type TransitionMap = Map Int   (Map (Char) [(Int,       Int)])

data MFA = MFA 
    { nstates :: Int
    , trans   :: TransitionMap
    , initial :: [Int]
    , final   :: [Int]
    } deriving Show


--                -> State ->  Char -> [(NextState, Add)]
nextstates :: MFA -> Int   ->  Char -> [(Int,       Int)]
nextstates mfa state ch = 
        fromMaybe [] (do
            chmap <- Map.lookup state (trans mfa)
            Map.lookup ch chmap)

-- merge two lists without duplicates
merge :: Ord a => [a] -> [a] -> [a]
merge l1 l2 = (Set.toList . Set.fromList) (l1 ++ l2)

-- do a run over a MFA without epsions
run :: String -> MFA -> [(Int,Int)]
run str mfa = run_helper [(i, 0) | i <- initial mfa] str mfa
    where 
        run_helper :: [(Int,Int)] -> String -> MFA -> [(Int,Int)]
        run_helper [] _ mfa = []
        run_helper state [] mfa = [(s, acc) | (s, acc) <- state, elem s (final mfa)]
        run_helper state (letter:xs) mfa = (run_helper ([(n, acc + a) | (s, acc) <- state, (n, a) <- nextstates mfa s letter]) xs mfa)

-- do a run over a MFA with epsilons
run_slow :: String -> MFA -> [(Int,Int)]
run_slow str mfa = run_slow_helper [] str mfa
    where
        run_slow_helper :: [(Int,Int)] -> String -> MFA -> [(Int,Int)]
        run_slow_helper [] _ mfa = []
        run_slow_helper state [] mfa =
            merge
                [(s, acc) | (s, acc) <- state, elem s (final mfa)]
                (run_slow_helper ([(n, acc + a) | (s, acc) <- state, (n, a) <- nextstates mfa s '\0']) [] mfa)
        run_slow_helper state (letter:xs) mfa = 
            merge
                (run_slow_helper ([(n, acc + a) | (s, acc) <- state, (n, a) <- nextstates mfa s letter]) xs mfa)
                (run_slow_helper ([(n, acc + a) | (s, acc) <- state, (n, a) <- nextstates mfa s '\0']) (letter:xs) mfa)


-- combine multiple transition functions
merge_trans :: [TransitionMap] -> TransitionMap
merge_trans = foldr1 $ Map.unionWith $ Map.unionWith merge

single_trans :: Int -> Char -> Int -> Int -> TransitionMap
single_trans s c n v =  Map.fromList [(s, Map.fromList [(c, [(n, v)])])]

fix_for_kleene :: MFA -> MFA
fix_for_kleene mfa =
    let i = (head (initial mfa))
        f = traceShowId $ fwd_epsilon mfa i
    in if (any (\x -> elem x (final mfa)) f)
           then (MFA (nstates mfa) (trans mfa) (initial mfa) (merge [i] (filter (\s -> not $ elem s f) (final mfa))))
           else mfa
       

-- -- create a MFA from a regulare expression over single letters
regex_to_mfa :: Int -> Regex -> MFA

regex_to_mfa s (Primitive c i) =
    MFA 2 (single_trans s c (s + 1) i) [s] [s + 1]

regex_to_mfa s (RSum r1 r2) =
    MFA (nstates1 + nstates2 + 1)
        (merge_trans 
            [ t1 , t2 
            , Map.fromList [(s, Map.fromList [('\0', [(qi, 0) | qi <- init1 ++ init2])])]])
        [s]
        (final1 ++ final2)
    where
        MFA nstates1 t1 init1 final1 = regex_to_mfa (s + 1)            r1
        MFA nstates2 t2 init2 final2 = regex_to_mfa (s + 1 + nstates1) r2

regex_to_mfa s (RMul r1 r2) =
    MFA (nstates1 + nstates2)
        (merge_trans [t1, t2, Map.fromList [(f1, Map.fromList [('\0', [(i2, 0) | i2 <- init2])]) | f1 <- final1]])
        init1
        final2
    where
        MFA nstates1 t1 init1 final1 = regex_to_mfa  s             r1
        MFA nstates2 t2 init2 final2 = regex_to_mfa (s + nstates1) r2

regex_to_mfa s (Kleene r) =
    MFA (nstates + 2)
        (merge_trans 
            [ t
            , (single_trans (s + 1) '\0' s 0)
            , Map.fromList [(s,  Map.fromList [('\0', [(qi, 0) | qi <- init])])]
            , Map.fromList [(qf, Map.fromList [('\0', [(s + 1, 0)])]) | qf <- (filter (/= (head init))final)]])
        [s]
        [s, s + 1]
    where
        MFA nstates t init final = fix_for_kleene $ regex_to_mfa (s + 2) r


--                       Visited ->     -> State ->

fwd_epsilon :: MFA -> Int -> [Int]
fwd_epsilon mfa state = fwd_helper [] mfa state
    where
        fwd_helper :: [Int]   -> MFA -> Int   -> [Int]
        fwd_helper visited mfa state = 
            let n = [a | (a, _) <- nextstates mfa state '\0', not $ elem a visited] 
            in  merge n (n >>= (fwd_helper (merge visited n) mfa))


remove_epsilons :: MFA -> MFA
remove_epsilons mfa = remove_epsilons_helper [] (trans mfa) (head (initial mfa)) mfa
    where
--                                Done  ->               -> CurrentState ->     -> 
        remove_epsilons_helper :: [Int] -> TransitionMap -> Int          -> MFA -> MFA
        remove_epsilons_helper done acc state mfa
            | state == nstates mfa = MFA (nstates mfa) 
                                         acc 
                                         (initial mfa)
                                         [s | s <- [0..nstates mfa-1], (elem s (final mfa)) || (any (\e -> elem e (final mfa)) (fwd_epsilon mfa s))]
            | otherwise = 
                let (done1, acc1) = rem1 done acc state mfa (fwd_epsilon mfa state)
                in remove_epsilons_helper done1 acc1 (state + 1) mfa 
        --         Done  -> Accumulate    -> Current ->     -> Remaining -> NextDone
        rem1 :: [Int] -> TransitionMap -> Int     -> MFA -> [Int]     -> ([Int], TransitionMap)
        rem1 done acc state mfa [] = let fwd = fwd_epsilon mfa state
                                         mem = catMaybes $ [Map.lookup s (acc) | s <- fwd]
                                         chmap = Map.lookup state acc
                                         x = do 
                                             chm <- chmap
                                             let noe = Map.delete '\0' chm
                                             return $ foldr1 (Map.unionWith merge) (noe:mem)
                                     in ((state:done), Map.alter (const x) state acc)
        rem1 done acc state mfa (x:xs)
           | elem x done = rem1 done acc state mfa xs
           | otherwise = let (done1, acc1) = rem1 done acc x mfa (fwd_epsilon mfa x)
                         in rem1 done1 acc1 state mfa xs
                      

lower :: Int -> [Int] -> [Int]
lower rm [] = []
lower rm (x:xs)
    | x <  rm = x:(lower rm xs)
    | x == rm = lower rm xs
    | x >  rm = (x - 1):(lower rm xs)
lower_trans :: Int -> TransitionMap -> TransitionMap
lower_trans rm m = Map.fromList [(if s > rm then s - 1 else s, Map.map (\ls -> [(if x < rm then x else x - 1,y) | (x,y) <- ls, x /= rm]) sm) | (s, sm) <- (Map.toList m), s /= rm]

remove_state :: Int -> MFA -> MFA
remove_state rm (MFA nstates trans init final)
    = MFA (nstates - 1) (lower_trans rm trans) (lower rm init) (lower rm final)



directly_reachable :: Int -> MFA -> [Int]
directly_reachable state mfa = fromMaybe [] $ do
    chm <- Map.lookup state (trans mfa)
    return $ (Set.toList . Set.fromList) [state |  (_, ls) <- (Map.toList chm), (state, _) <- ls]


reachable_states :: [Int] -> [Int] -> MFA -> [Int]
reachable_states visited [] mfa = visited

reachable_states visited (x:xs) mfa
    | elem x visited = reachable_states visited xs mfa
    | otherwise = reachable_states (x:visited) 
                                   (filter (\n -> not $ elem n visited) (merge (directly_reachable x mfa) xs))
                                   mfa

remove_unreachable_states :: MFA -> MFA
remove_unreachable_states mfa = let reachable = reachable_states [] (initial mfa) mfa
                                    unreachable = sort [s | s <- [0..(nstates mfa)-1], not $ elem s reachable]
                                in foldr remove_state mfa unreachable


-- Regex parser
data Parser a = Parser { parse :: String -> Maybe (a, String) }

instance Functor Parser  where
    fmap fn (Parser p1) = Parser (\str -> do
        (a, rem) <- p1 str;
        return (fn a, rem))

instance Applicative Parser where
    pure val = Parser $ \str -> Just (val, str)
    p1 <*> p2 = Parser (\str -> do
        (fn, rem1) <- parse p1 str
        (v, rem2) <- parse p2 rem1
        return (fn v, rem2))

parse_char_if :: (Char -> Bool) -> Parser Char
parse_char_if pred = Parser (\str -> case str of
    [] -> Nothing
    (x:xs) | pred x -> Just(x, xs)
           | otherwise -> Nothing)

repeatp :: Parser a -> Parser [a]
repeatp (Parser p) = Parser (\str -> case (p str) of
                                Nothing -> (Just ([], str))
                                Just (val, rem) -> let Just (lst, r) = parse (repeatp (Parser p)) rem
                                                   in Just (val:lst, r))
parse_word = repeatp $ parse_char_if isLower
parse_number = fmap read (repeatp $ parse_char_if isDigit)
parse_primitive = fn <$> parse_word <*> parse_char_if (== ':') <*> parse_number
    where fn (x:[]) _ n = Primitive x n
          fn (x:xs) _ n = RMul (Primitive x 0) (fn xs ':' n)



--             IsSum  -> Last was bracket -> Stack   -> Remaining Tokens -> (Output, Remaining)
parse_regex :: Bool   -> Bool             -> [Regex] -> String           -> (Regex,  String)
parse_regex _ _ (x:xs) [] = (x, [])
parse_regex _ _ (x:xs) (')':ys) = (x, ys)
parse_regex b1 b2 stack ('|': ys) = parse_regex True b2 stack ys

parse_regex b1 b2 (x:xs) ('*': ys) = parse_regex False False 
    (if b2 then (Kleene x:xs)
          else (case x of
                   Primitive _ _ -> (Kleene x:xs)
                   Kleene _ -> (Kleene x:xs)
                   RSum l r -> ((RSum l (Kleene r)):xs)
                   RMul l r -> ((RMul l (Kleene r)):xs))) ys

parse_regex b1 b2 stack ('(': ys) = let (r, rem) =  parse_regex False False [] ys
                                    in parse_regex False True 
                                                   (case stack of 
                                                        [] -> [r]
                                                        (x:xs) -> (((if b1 then RSum else RMul) x r):xs)) rem

parse_regex b1 b2 stack word = case parse parse_primitive word of
    Just (r, rem) -> parse_regex False False (case stack of 
        [] -> [r]
        (x:xs) -> (((if b1 then RSum else RMul) x r):xs)) rem



main :: IO ()
main = do
    (regex_txt:input:ys) <- getArgs

    let (regex, _) = parse_regex False False [] regex_txt
    let mfa0 = regex_to_mfa 0 regex
    let mfa1 = remove_epsilons  mfa0
    let mfa = remove_unreachable_states mfa1

    putStrLn $ "Transducer has " ++ show (nstates mfa) ++ " states."

    let result = run input mfa
    putStr "Result: "
    print $ [acc | (_, acc) <- result]
