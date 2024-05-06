#!/bin/sh

OPTS="-background white -alpha remove -alpha off -quality 90"

convert -density 300 -append CigaretteSmokers.pdf $OPTS -crop 1570x1860+520+520 images/CigaretteSmokers.png
convert -density 300 -append Blinker.pdf $OPTS -crop 1570x2240+520+520 images/Blinker.png
convert images/Blinker.png -crop 1570x2360+520+520 images/Blinker.png
convert -density 300 -append GameOfLife.pdf $OPTS -crop 1570x1860+520+520 images/GameOfLife.png
convert -density 300 -append Requirements.pdf $OPTS -crop 1570x1660+520+520 images/Requirements.png
convert -density 300 -append CheckRequirements.pdf $OPTS -crop 1570x1000+520+520 images/CheckRequirements.png
convert -density 300 -append SlidingPuzzles.pdf $OPTS -crop 1570x2250+520+520 images/SlidingPuzzles.png
convert -density 300 -append Chameneos.pdf $OPTS -crop 1770x2260+520+520 images/Chameneos.png
convert images/Chameneos.png -crop 1770x2960+520+520 images/Chameneos.png
# DIV generated with -textwidth 420
convert -density 300 -append Watchdog.dvi $OPTS -crop 1870x2260+520+520 images/Watchdog.png
convert images/Watchdog.png -crop 1870x3660+520+520 images/Watchdog.png
# DIV generated with -textwidth 460
convert -density 300 -append Scheduler.dvi $OPTS -crop 2000x2260+520+520 images/Scheduler.png
convert images/Scheduler.png -crop 2000x4660+520+520 images/Scheduler.png
