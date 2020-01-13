#!/bin/sh

convert -density 300 CigaretteSmokers.pdf -quality 90 -crop 1570x2060+520+520 images/CigaretteSmokers.png
convert -density 300 Blinker.pdf -quality 90 -crop 1570x2240+520+520 images/Blinker.png
convert -density 300 GameOfLife.pdf -quality 90 -crop 1570x1860+520+520 images/GameOfLife.png
