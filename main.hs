import Data.Maybe
import Data.List
import Data.Char
import Control.Applicative
import Control.Monad
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
            deriving (Show) --                       State             [(NextState, Add)]
type TransitionMap = Map Int   (Map (Char) [(Int,       Int)])

data MFA = MFA 
    { nstates :: Int
    , trans   :: TransitionMap
    , initial :: Int
    , final   :: [Int]
    , final_add :: Map Int Int
    } deriving Show



--                -> State ->  Char -> [(NextState, Add)]
nextstates :: MFA -> Int   ->  Char -> [(Int,       Int)]
nextstates mfa state ch = 
        fromMaybe [] (do
            chmap <- Map.lookup state (trans mfa)
            Map.lookup ch chmap)

--              -> State -> Acc
finaladd :: MFA -> Int   -> Int
finaladd mfa s = fromMaybe 0 $ Map.lookup s (final_add mfa)

-- merge two lists without duplicates
-- merge l1 l2 = (Set.toList . Set.fromList) (l1 ++ l2)
merge :: Eq a => [a] -> [a] -> [a]
merge a b = merge_helper [] a b
    where merge_helper :: Eq a => [a] -> [a] -> [a] -> [a]
          merge_helper v [] [] = []
          merge_helper v [] r = merge_helper v r []
          merge_helper v (x:xs) r = if (elem x v) then merge_helper v xs r else x:(merge_helper (x:v) r xs)


-- do a run over a MFA without epsions
run :: String -> MFA -> [(Int,Int)]
run str mfa = run_helper [(initial mfa, 0)] str mfa
    where 
        run_helper :: [(Int,Int)] -> String -> MFA -> [(Int,Int)]
        run_helper [] _ mfa = []
        run_helper state [] mfa =  [(s, acc + finaladd mfa s) | (s, acc) <- state, elem s (final mfa)]
        run_helper state (letter:xs) mfa = run_helper ([(n, acc + a) | (s, acc) <- state, (n, a) <- nextstates mfa s letter]) xs mfa

-- do a run over a MFA with epsilons
run_slow :: String -> MFA -> [(Int,Int)]
run_slow str mfa = run_slow_helper [(initial mfa,0)] str mfa
    where
        run_slow_helper :: [(Int,Int)] -> String -> MFA -> [(Int,Int)]
        run_slow_helper [] _ mfa = []
        run_slow_helper state [] mfa =
            merge
                [(s, acc + finaladd mfa s) | (s, acc) <- state, elem s (final mfa)]
                (run_slow_helper ([(n, acc + a) | (s, acc) <- state, (n, a) <- nextstates mfa s '\0']) [] mfa)
        run_slow_helper state (letter:xs) mfa = 
            merge
                (run_slow_helper ([(n, acc + a) | (s, acc) <- state, (n, a) <- nextstates mfa s letter]) xs mfa)
                (run_slow_helper ([(n, acc + a) | (s, acc) <- state, (n, a) <- nextstates mfa s '\0']) (letter:xs) mfa)


-- combine multiple transition functions
merge_trans :: [TransitionMap] -> TransitionMap
merge_trans = foldr1 $ Map.unionWith $ Map.unionWith merge

--              From ->      -> To  -> Num ->
single_trans :: Int  -> Char -> Int -> Int -> TransitionMap
single_trans s c n v =  Map.fromList [(s, Map.fromList [(c, [(n, v)])])]

-- -- create a MFA from a regulare expression over single letters
regex_to_mfa :: Int -> Regex -> MFA

regex_to_mfa s (Primitive c i) =
    MFA 2 (single_trans s c (s + 1) i) s [s + 1] (Map.fromList [])

regex_to_mfa s (RSum r1 r2) =
    MFA (nstates1 + nstates2 + 1)
        (merge_trans 
            [ t1 , t2 
            , Map.fromList [(s, Map.fromList [('\0', [(qi, 0) | qi <- [init1, init2]])])]])
        s (final1 ++ final2) (Map.fromList [])
    where
        MFA nstates1 t1 init1 final1 _ = regex_to_mfa (s + 1)            r1
        MFA nstates2 t2 init2 final2 _ = regex_to_mfa (s + 1 + nstates1) r2

regex_to_mfa s (RMul r1 r2) =
    MFA (nstates1 + nstates2)
        (merge_trans [t1, t2, Map.fromList [(f1, Map.fromList [('\0', [(init2, 0)])]) | f1 <- final1]])
        init1
        final2
        (Map.fromList [])
    where
        MFA nstates1 t1 init1 final1 _ = regex_to_mfa  s             r1
        MFA nstates2 t2 init2 final2 _ = regex_to_mfa (s + nstates1) r2

regex_to_mfa s (Kleene r) =
    MFA (nstates + 2)
        (merge_trans 
            [ t
            , (single_trans s '\0' (s+1) 0)
            , (single_trans s '\0' init 0)
            , Map.fromList [(qf, Map.fromList [('\0', [(s + 1, 0)])]) | qf <- final]
            , Map.fromList [(qf, Map.fromList [('\0', [(init, 0)])]) | qf <- final]])
        s [s + 1]
        (Map.fromList [])
    where
        MFA nstates t init final _ = regex_to_mfa (s + 2) r 



-- Find a mutually reachable with only epsilon:0 transitions state
-- We use this to collapse these states into one
find_equiv :: MFA -> Int -> Maybe (Int,Int)
find_equiv mfa state = helper mfa state 0 state []
    where
--                    -> State -> Acc -> Target -> Visited -> Equiv
        helper :: MFA -> Int   -> Int -> Int    -> [Int]   -> Maybe (Int,Int)
        helper mfa current acc target vis = 
            let next = [(n,v+acc) | (n,v) <- nextstates mfa current '\0']
            in if (elem target [n|(n,_)<-next]) 
                   then Just (current, acc)
                   else let unvis = [(x,a) | (x,a) <- next, not $ elem x vis]
                        in if unvis == [] 
                               then Nothing
                               else msum [helper mfa n a target (current:vis) | (n,a) <- unvis]


--              -> State1 -> State2 ->
collapse :: MFA -> Int    -> Int    -> MFA

collapse mfa s1 s2 =
    let p = Map.map 
               (\chmap -> (Map.map (\t -> [(if n == s2 then s1 else n,val) | (n, val) <- t]) chmap)) 
               (trans mfa)
        p2 = (merge_trans [ p, Map.fromList [(s1, fromMaybe (Map.fromList []) (Map.lookup s2 p))]])
        p3 = Map.alter (fmap (\m -> Map.alter (fmap $ filter (/= (s1,0))) '\0' m)) s1 p2

        m1 = MFA (nstates mfa)
                 p3
                 (if (initial mfa) == s2 then s1 else (initial mfa))
                 (final mfa)
                 (Map.fromList [])
    in remove_state s2 m1

-- Collapse all equivalent epsilon:0 states
-- The bool return value is true if MFA is infinitely ambiguous
collapse_all :: MFA -> (MFA, Bool)
collapse_all mfa = helper 0 mfa False
    where helper :: Int -> MFA -> Bool -> (MFA, Bool)
          helper n mfa inf =
              if n == nstates mfa
                  then (mfa, inf)
                  else case find_equiv mfa n of
                      Just (s2,a) -> if a == 0 
                                         then helper (if (n > s2) then (n - 1) else n) (collapse mfa n s2) inf
                                         else helper (n + 1) mfa True
                      Nothing     -> helper (n + 1) mfa inf

    
fwd_epsilon :: MFA -> Int -> [(Int,Int)]
fwd_epsilon mfa state = fwd_helper [] mfa state
    where
        fwd_helper :: [Int] -> MFA -> Int -> [(Int,Int)]
        fwd_helper visited mfa state = 
            let n = [(a, val) | (a, val) <- nextstates mfa state '\0', not $ elem a visited] 
            in  (Set.toList . Set.fromList)  (n ++ [(an, v1+vn) |(st, v1) <- n, (an, vn) <- fwd_helper (merge visited [s|(s,_)<-n]) mfa st])


remove_epsilons :: MFA -> MFA
remove_epsilons mfa = remove_epsilons_helper [] (trans mfa) (initial mfa) mfa
    where
--                                Done  ->               -> CurrentState ->     -> 
        remove_epsilons_helper :: [Int] -> TransitionMap -> Int          -> MFA -> MFA
        remove_epsilons_helper done acc state mfa
            | state == nstates mfa = 
                MFA (nstates mfa) 
                   acc 
                   (initial mfa)
                   [s | (s,acc) <- f]
                   (Map.fromList f)
                   -- [s | s <- [0..nstates mfa-1], (elem s (final mfa)) || (any (\e -> elem e (final mfa)) [s | (s,_) <- (fwd_epsilon mfa s)])]
                   -- (Map.fromList [])
            | otherwise = 
                let (done1, acc1) = rem1 done acc state mfa [x | (x,_) <- (fwd_epsilon mfa state)]
                in remove_epsilons_helper done1 acc1 (state + 1) mfa 
           where 
               oldf = [(s, finaladd mfa s) | s <- final mfa]
               newf = [(s, finaladd mfa s2 + a2) | s <- [0..nstates mfa-1], (s2, a2) <- (fwd_epsilon mfa s), elem s2 (final mfa)]
               f = merge oldf newf

        --      Done  -> Accumulate    -> Current ->     -> Remaining -> NextDone
        rem1 :: [Int] -> TransitionMap -> Int     -> MFA -> [Int]     -> ([Int], TransitionMap)
        rem1 done acc state mfa [] = 
             let fwd = fwd_epsilon mfa state
                 mem = catMaybes $ [(Map.map (\lst -> [(x,y+a) | (x,y) <- lst])) <$> Map.lookup s (acc) | (s,a) <- fwd]
                 chmap = Map.lookup state acc
                 x = do 
                    chm <- chmap
                    let noe = Map.delete '\0' chm
                    return $ foldr1 (Map.unionWith merge) (noe:mem)
             in ((state:done), Map.alter (const x) state acc)
        rem1 done acc state mfa (x:xs)
           | elem x done = rem1 done acc state mfa xs
           | otherwise = let (done1, acc1) = rem1 done acc x mfa [x | (x, _) <- (fwd_epsilon mfa x)]
                         in rem1 done1 acc1 state mfa xs
                      


remove_state :: Int -> MFA -> MFA
remove_state rm (MFA nstates trans init final fa)
    = MFA (nstates - 1) (lower_trans rm trans) (if rm < init then init - 1 else init) (lower rm final) fa -- TODO 
    where
        lower :: Int -> [Int] -> [Int]
        lower rm [] = []
        lower rm (x:xs)
            | x <  rm = x:(lower rm xs)
            | x == rm = lower rm xs
            | x >  rm = (x - 1):(lower rm xs)
        lower_trans :: Int -> TransitionMap -> TransitionMap
        lower_trans rm m = Map.fromList [(if s > rm then s - 1 else s, Map.map (\ls -> [(if x < rm then x else x - 1,y) | (x,y) <- ls, x /= rm]) sm) | (s, sm) <- (Map.toList m), s /= rm]


directly_reachable :: Int -> MFA -> [Int]
directly_reachable state mfa = fromMaybe [] $ do
    chm <- Map.lookup state (trans mfa)
    return $ (Set.toList . Set.fromList) [state |  (_, ls) <- (Map.toList chm), (state, _) <- ls]



remove_unreachable_states :: MFA -> MFA
remove_unreachable_states mfa = let reachable = reachable_states [] [initial mfa] mfa
                                    unreachable = sort [s | s <- [0..(nstates mfa)-1], not $ elem s reachable]
                                in foldr remove_state mfa unreachable
    where 
        reachable_states :: [Int] -> [Int] -> MFA -> [Int]
        reachable_states visited [] mfa = visited
        
        reachable_states visited (x:xs) mfa
            | elem x visited = reachable_states visited xs mfa
            | otherwise = reachable_states (x:visited) 
                                           (filter (\n -> not $ elem n visited) (merge (directly_reachable x mfa) xs))
                                           mfa


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

parse_word = repeatp $ parse_char_if (\ch -> isLower ch || isUpper ch || ch == '#')
parse_number = fmap read (repeatp $ parse_char_if isDigit)

parse_primitive = fn <$> parse_word <*> parse_char_if (== ':') <*> parse_number
    where
          fn ['#']  _ n = Primitive '\0' n
          fn (x:[]) _ n = Primitive x n
          fn (x:xs) _ n = RMul (Primitive x 0) (fn xs ':' n)


--                           Current, Next, Val1, Val2
type SquaredTransitionMap = [(Int,    Int,  Int,  Int)]

data SMFA = SMFA
    { strans     :: SquaredTransitionMap
    , sinitial   :: Int
    , sfinal     :: [Int]
    -- , sfinal_add :: Map Int Int
    } deriving Show

square_auto :: MFA -> SMFA
square_auto mfa = SMFA stmap
                       (sstate (initial mfa) (initial mfa)) 
                       [sstate f1 f2 | f1 <- final mfa, f2 <- final mfa]
    where
        sstate :: Int -> Int -> Int
        sstate s1 s2 = (nstates mfa) * s1 + s2

--           Previous     Advance      NextDelta
        w :: (Int,Int) -> (Int,Int) -> (Int,Int)
        w (a,b) (a1, b1) = 
            let an = a + a1
                bn = b + b1
                m = min an bn
            in (an - m, bn - m)

        tlist = [(p, ch, n, v)  | (p, m1) <- Map.toList (trans mfa), (ch, l) <- Map.toList m1, (n, v) <- l]
        stmap = [(sstate p1 p2, sstate n1 n2, v1, v2) | (p1, ch, n1, v1) <- tlist, (p2, ch, n2, v2) <- tlist]


parse_regex :: String -> Regex
parse_regex str = rgh [] [] str
    where
        --     OutputQueue -> OpStack -> Remaining -> 
        rgh :: [Regex]     -> [Char]  -> String    -> Regex
        pop_until_openbracket :: [Regex] -> [Char] -> ([Regex],[Char])
        
        rgh [q] [] [] = q
        
        rgh (q2:q1:qs) ('.':xs) [] = rgh ((RMul q1 q2):qs) xs []
        rgh (q2:q1:qs) ('|':xs) [] = rgh ((RSum q1 q2):qs) xs []
        
        rgh (q1:qs) s ('*':strs) = rgh ((Kleene q1):qs) s strs
        
        rgh q s ('.':strs) = rgh q ('.':s) strs
        rgh q s ('|':strs) = rgh q ('|':s) strs
        rgh q s ('(':strs) = rgh q ('(':s) strs
        
        rgh q s (')': strs) = rgh q1 s1 strs where (q1, s1) = pop_until_openbracket q s

        rgh q s str = let Just (r,rem) = (parse parse_primitive str) in rgh (r:q) s rem

        pop_until_openbracket q ('(':s) = (q,s)
        pop_until_openbracket (q2:q1:q) ('.':s) = pop_until_openbracket ((RMul q1 q2):q) s
        pop_until_openbracket (q2:q1:q) ('|':s) = pop_until_openbracket ((RSum q1 q2):q) s



main :: IO ()
main = do
    (regex_txt:input:ys) <- getArgs
    let regex = parse_regex regex_txt
    let mfa0 = regex_to_mfa 0 regex

    let (mfa1,inf) = collapse_all mfa0
    putStrLn $ "The MFA has " ++ show (nstates mfa1) ++ " states"

    if inf then do
        putStrLn $ "It is infinitely ambiguous"
        putStr $ "Output: "
        print $ [acc | (_, acc) <- run_slow input mfa0]
    else do
        -- print mfa0
        let mfa2 =  remove_epsilons mfa1
        let mfa3 =  traceShowId $ remove_unreachable_states mfa2
        print $ square_auto mfa3
        putStr $ "Output: "
        print $ [acc | (_, acc) <- run input mfa3]

        -- print $ square_auto $ mfa2

    return ()
