{-# OPTIONS --guardedness #-}

module compile where

open import print
open import tests

open import IO

main : Main
main = run (putStrLn (format-steps test3))

