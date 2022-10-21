
This package has been created by Berno Reitsma under supervision and with the essential help of Steffen Müller.
It contains an implementation of an algorithm to compute the rational torsion subgroup of Jacobians of hyperelliptic 
curves of genus 3 in the MAGMA Computational Algebra System. (See link below)

This implementation is part of the goal of Berno's Master's Thesis, available at
https://fse.studenttheses.ub.rug.nl/23649/1/mMATH_2020_ReitsmaB.pdf. 
The paper 'Computing torsion subgroups of Jacobians of hyperelliptic curves of genus three' by Steffen Müller and 
Berno Reitsma (see the file 'g3hyptorsion.pdf') contains a shortened and generalized description of the algorithm 
and fixes some issues with the original version, some of which were pointed out to us by Michael Stoll.

The algorithm is essentially a genus 3 version of the algorithm for genus 2 described in section 11 of 
Michael Stoll - On the Height constant for curves of genus two; Acta Arith. 90, 183-201 (1999).
The code mainly expands upon existing code for genus 2 hyperelliptic curves due to Stoll and contained in Magma.
For the generalization, we have used the Kummer variety functionality created and hosted by Stoll on his 
webpage (linked below), mainly the files G3Hyp.m and G3HypHelp.m, most of which is theoretically explained in 
Michael Stoll - An Explicit Theory of Heights for Hyperelliptic Jacobians of Genus Three - 
In Algorithmic and experimental methods in algebra, geometry, and number theory, 665-715, Springer, Cham, 2017

WARNING: some of the Verbose printing on supporting functionality may return errors.

Important files are:
- torsion3.m contains the functions that compute the rational torsion subgroup of jacobians of hyperelliptic curves of genus 3.
- curvetest.m is set up such that one can easily test a curve.
- gen3databasecomputations.m runs through the database of Andrew V. Sutherland, gce_genus3_hyperelliptic.txt
	(linked below) and outputs to the file output.txt. gen3databasecomputations runs through almost 70000
	curves, so this requires a long computation.
- database.txt contains a database for all elementary divisors of the rational torsion subgroups that are in 
	the file gce_genus3_hyperelliptic.txt, found under the name "genus 3 hyperelliptic curves of small discriminant over Q" 
	at the webpage of Andrew Sutherland, in the same format, but now containing a list of invariant factors at the end, in between the "[]".
	It is the output file from running gen3databasecomputations.m, renamed to prevent overwriting.
- searchresults.m and additional.m contain code to verify the claims in Section 5.3 of 
- g3torsion.pdf is the above-mentioned paper 'Computing torsion subgroups of Jacobians of hyperelliptic curves of genus three' 
	by Steffen Müller and Berno Reitsma.

Links:
MAGMA Computational Algebra System:
	http://magma.maths.usyd.edu.au/magma/
MAGMA-related directory of Michael Stoll:
	http://www.mathe2.uni-bayreuth.de/stoll/magma/index.html
genus 3 hyperelliptic curves of small discriminant over Q, hosted by Andrew V. Sutherland:
	https://math.mit.edu/~drew/gce_genus3_hyperelliptic.txt

If a comment in the code references a section, theorem, lemma, etc, this refers to my Master's Thesis
