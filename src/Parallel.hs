{-# LANGUAGE FlexibleContexts #-}
module Parallel (bitonicPar, mergePar, hybridPar, quickPar) where
import           Control.DeepSeq             (force)
import           Control.Monad               (when)
import           Control.Monad.IO.Class
import           Control.Monad.Par.Class
import           Control.Monad.Par.IO
import           Control.Parallel.Strategies
import           Data.List.Split             (chunksOf)
import           Data.Vector                 ((!))
import qualified Data.Vector                 as V
import qualified Data.Vector.Mutable         as M
import qualified Data.Vector.Split           as S
import           Sequential                  (quickSeq)
import           Utils                       (fillBitonic)
import qualified Control.Monad.State.Lazy    as S

bitonicPar :: (NFData a, Ord a) => a -> V.Vector a -> IO (V.Vector a)
bitonicPar = (bitonic .) . fillBitonic

bitonic :: Ord a => V.Vector a -> IO (V.Vector a)
bitonic v = do
    o <- V.thaw v
    runParIO $ bitonicSort' o 0 (V.length v) True (0 :: Integer)
    V.freeze o
    where
        bitonicSort' o low cnt dir l =
            when (cnt > 1) $ do
                let k = cnt `div` 2
                if l < 7 then do
                    a <- spawn $ bitonicSort' o low k True (l+1)
                    b <- spawn $ bitonicSort' o (low + k) k False (l+1)
                    get a
                    get b
                else do
                    bitonicSort' o low k True (l+1)
                    bitonicSort' o (low + k) k False (l+1)
                bitonicMerge o low cnt dir l
        bitonicMerge o low cnt dir l =
            when (cnt > 1) $ do
                let k = cnt `div` 2
                loopSwap o low low k dir
                if l < 7 then do
                    a <- spawn $ bitonicMerge o low k dir (l+1)
                    b <- spawn $ bitonicMerge o (low+k) k dir (l+1)
                    get a
                    get b
                else do
                    bitonicMerge o low k dir (l+1)
                    bitonicMerge o (low+k) k dir (l+1)
        loopSwap o low i k dir =
            when (i < low + k) $ do
                loopSwap o low (i+1) k dir
                liftIO $ compareAndSwap o i (i+k) dir
        compareAndSwap o i j dir = do
            oi <- M.read o i
            oj <- M.read o j
            when (dir == (oi > oj)) $ M.swap o i j

hybridPar :: (NFData a, Ord a) => V.Vector a -> V.Vector a
hybridPar v = merge $ V.fromList $ parMap rdeepseq quickSeq chunks
    where
    n = V.length v
    chunks = S.chunksOf (n `div` 32) v

quickPar :: (NFData a, Ord a) => V.Vector a -> V.Vector a
quickPar x = runEval $ quickPar' chunks
    where
    quickPar' :: (NFData a, Ord a) => [V.Vector a] -> Eval (V.Vector a)
    quickPar' [] = return V.empty
    quickPar' [v] = rpar (quickSeq v)
    quickPar' (v:vs) = do
            let p = V.head v
            vs' <- parList rdeepseq (V.partition (<p) <$> (V.tail v:vs))
            lower <- parList rdeepseq (fst <$> vs')
            upper <- parList rdeepseq (snd <$> vs')
            lower' <- parList rdeepseq (filter (not . null) $ V.concat <$> chunksOf 2 lower)
            upper' <- parList rdeepseq (filter (not . null) $ V.concat <$> chunksOf 2 upper)
            lower'' <- quickPar' lower'
            upper'' <- quickPar' upper'
            rpar ((lower'' `V.snoc` p) V.++ upper'')
    n = V.length x
    chunks = S.chunksOf (n `div` 32) x

mergePar :: (NFData a, Ord a) => V.Vector a -> V.Vector a
mergePar = merge . runs

runs :: Ord a => V.Vector a -> V.Vector (V.Vector a)
runs x = V.create $ do
    o <- M.new (V.length x)
    runs' 1 x 0 o
    where
        runs' i v k o
            | i < V.length v =
                if v!(i-1) <= v!i then
                    asc (i-1) i k o
                else
                    dsc (i-1) i k o
            | otherwise = return $ M.slice 0 k o
        asc s i k o =
            if i < V.length x && x!(i-1) <= x!i then
                asc s (i+1) k o
            else do
                M.write o k (V.slice s (i-s) x)
                runs' (i+1) x (k+1) o
        dsc s i k o =
            if i < V.length x && x!(i-1) > x!i then
                dsc s (i+1) k o
            else do
                M.write o k (V.reverse $ V.slice s (i-s) x)
                runs' (i+1) x (k+1) o


merge :: (NFData a, Ord a) => V.Vector (V.Vector a) -> V.Vector a
merge x = runEval (merge' (0::Integer) x)
    where
    merge' l v
       | n > 1 = do
            a' <- merge' (l+1) a >>= if l < 15 then rpar else rseq
            b' <- merge' (l+1) b >>= if l < 15 then rpar else rseq
            if l < 1 then computeExchange a' b' else return $ merge2 a' b'
        | otherwise = return $ v!0
        where
        n = V.length v
        a = V.slice 0 (n `div` 2) v
        b = V.slice (n `div` 2) (n - n `div` 2) v

merge2 :: Ord a => V.Vector a -> V.Vector a -> V.Vector a
merge2 a b = V.create $ do
    v <- M.new (V.length a + V.length b)
    a' <- V.thaw a
    b' <- V.thaw b
    go a' b' 0 0 v
    return v
        where go a' b' i j v
                | i < V.length a && j < V.length b = do
                    ai <- M.unsafeRead a' i
                    bj <- M.unsafeRead b' j
                    if ai <= bj then do
                        M.unsafeWrite v (i+j) ai
                        go a' b' (i+1) j v
                    else do
                        M.unsafeWrite v (i+j) bj
                        go a' b' i (j+1) v
                | i < V.length a = do
                    ai <- M.unsafeRead a' i
                    M.unsafeWrite v (i+j) ai
                    go a' b' (i+1) j v
                | j < V.length b = do
                    bj <- M.unsafeRead b' j
                    M.unsafeWrite v (i+j) bj
                    go a' b' i (j+1) v
                | otherwise = return ()


computeExchange :: (NFData a, Ord a) => V.Vector a -> V.Vector a -> Eval (V.Vector a)
computeExchange a b = (`fmap` evalUpper) . (V.++) =<< evalLower 
    where
    evalLower = fpar $ lower 
    evalUpper = fpar $ upper 
    lower = pickAll (<=) a b (V.enumFromN (0::Int) n2) 
    upper = V.reverse $ pickAll (>=) (V.reverse a) (V.reverse b) (V.enumFromN (0::Int) (n-n2))
    pickAll f x y s = S.evalState (V.sequence $ (const $ pick f x y) <$> s) (0::Int,0::Int)
    pick f x y = S.get >>= pick' f x y
    pick' f x y (i, j)
        | i < V.length x && j < V.length y = pick2 f x y
        | i < V.length x = S.modify incI >> return (x!i)
        | otherwise = S.modify incJ >> return (y!j)
    pick2 f x y = do
        (i, j) <- S.get
        if f (x!i) (y!j) then 
            S.modify incI >> return (x!i) 
        else 
            S.modify incJ >> return (y!j)
    incI (i, j) = (i+1, j)
    incJ (i, j) = (i, j+1)
    n2 = n `div` 2
    n = V.length a + V.length b
    fpar = rpar . force

