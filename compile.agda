{-# OPTIONS --guardedness #-}

module compile where

open import print
open import tests

open import IO

my-test = test3

main : Main
main = run (putStrLn (format-steps my-test))

