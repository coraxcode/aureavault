#!/bin/sh
# Build AureaVault (SQLite edition). Needs only gcc; SQLite is bundled.
gcc -std=c99 -O2 -D_FORTIFY_SOURCE=2 aureavault.c sqlite3.c -o aureavault -lpthread
echo "Built ./aureavault"
