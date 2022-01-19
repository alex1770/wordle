all:: wordle wordle-hard
deb:: wordle wordle-hard

COMMITDESC:= "\"$(shell git log -1 --pretty=format:'%h %ad' --date=iso --abbrev=12)\""

# 'gitdescription' is updated when TAGDESC and COMMITDESC change, so add it as a
# dependency to files that use these tags, to force recompilation when they change
PREVDESC:= $(shell [ -f gitdescription ] && cat gitdescription)
CURRDESC:= $(TAGDESC) $(COMMITDESC)
ifneq ($(CURRDESC),$(PREVDESC))
  $(shell echo '$(CURRDESC)' > gitdescription)
endif

CFLAGS:= -std=c++14 -Wall -DCOMMITDESC=$(COMMITDESC)
ifneq ($(filter deb,$(MAKECMDGOALS)),)
  CFLAGS:= $(CFLAGS) -g
else
  CFLAGS:= $(CFLAGS) -O3
endif

wordle: wordle.cpp Makefile gitdescription
	g++ -o wordle wordle.cpp $(CFLAGS)

wordle-hard: wordle-hard.cpp Makefile gitdescription
	g++ -o wordle-hard wordle-hard.cpp $(CFLAGS)
