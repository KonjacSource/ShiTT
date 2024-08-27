module Common where 

(>>>) :: [a] -> a -> [a]
xs >>> x = xs ++ [x]

revCase :: [a] -> b -> ([a] -> a -> b) -> b
revCase ls emp nonemp 
  | null ls = emp 
  | otherwise = nonemp (init ls) (last ls)


impossible :: a 
impossible = error "Impossible"