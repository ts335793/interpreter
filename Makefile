all:
	bnfc -p BNFC Language.cf
	happy -gca BNFC/ParLanguage.y
	alex -g BNFC/LexLanguage.x
	(cd BNFC/; latex DocLanguage.tex; dvips DocLanguage.dvi -o DocLanguage.ps)
	ghc --make BNFC/TestLanguage.hs -o BNFC/TestLanguage
	ghc -Wall Main.hs -o interpreter
clean:
	-rm -f BNFC/*.log BNFC/*.aux BNFC/*.hi BNFC/*.o BNFC/*.dvi
	-rm -f BNFC/DocLanguage.ps
distclean: clean
	-rm -f BNFC/DocLanguage.* BNFC/LexLanguage.* BNFC/ParLanguage.* BNFC/LayoutLanguage.* BNFC/SkelLanguage.* BNFC/PrintLanguage.* BNFC/TestLanguage.* BNFC/AbsLanguage.* BNFC/TestLanguage BNFC/ErrM.* BNFC/SharedString.* BNFC/Language.dtd BNFC/XMLLanguage.* Makefile*
	-rmdir -p BNFC/
