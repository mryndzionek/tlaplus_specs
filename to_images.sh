#!/bin/sh

convert -density 300 -append CigaretteSmokers.pdf -quality 90 -crop 1570x2060+520+520 images/CigaretteSmokers.png
convert -density 300 -append Blinker.pdf -quality 90 -crop 1570x2240+520+520 images/Blinker.png
convert images/Blinker.png -crop 1570x2360+520+520 images/Blinker.png
convert -density 300 -append GameOfLife.pdf -quality 90 -crop 1570x1860+520+520 images/GameOfLife.png
convert -density 300 -append Requirements.pdf -quality 90 -crop 1570x1660+520+520 images/Requirements.png
convert -density 300 -append CheckRequirements.pdf -quality 90 -crop 1570x1000+520+520 images/CheckRequirements.png
convert -density 300 -append SlidingPuzzles.pdf -quality 90 -crop 1570x2250+520+520 images/SlidingPuzzles.png
convert -density 300 -append Chameneos.pdf -quality 90 -crop 1770x2260+520+520 images/Chameneos.png
convert images/Chameneos.png -crop 1770x2960+520+520 images/Chameneos.png
