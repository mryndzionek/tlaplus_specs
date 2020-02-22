#!/bin/sh

convert -density 300 CigaretteSmokers.pdf -quality 90 -crop 1570x2060+520+520 images/CigaretteSmokers.png
convert -density 300 Blinker.pdf -quality 90 -crop 1570x2240+520+520 images/Blinker.png
convert -density 300 GameOfLife.pdf -quality 90 -crop 1570x1860+520+520 images/GameOfLife.png
convert -density 300 Requirements.pdf -quality 90 -crop 1570x1660+520+520 images/Requirements.png
convert -density 300 CheckRequirements.pdf -quality 90 -crop 1570x1000+520+520 images/CheckRequirements.png
convert -density 300 SlidingPuzzles.pdf -quality 90 -crop 1570x2250+520+520 images/SlidingPuzzles.png
