#!/bin/sh
xpdf -remote viewer main.pdf 2>/dev/null &
./tw main
