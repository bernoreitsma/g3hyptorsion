NOTE:
There is an issue with the computation of 2-torsion points. This means that the actual rational 2-torsion group may be larger than suggested by the current code. We have hidden the current results. If you still want to check out the results with this warning in mind, you can check out the commit history.
We are working on a fix

This package has been created by Berno Reitsma under supervision and with the essential help of dr. J.S. (Steffen) Müller.
This implementation is part of the goal of Berno's Master Thesis, available at
https://fse.studenttheses.ub.rug.nl/23649/1/mMATH_2020_ReitsmaB.pdf.

It contains a way to compute the rational torsion subgroup of jacobians of hyperelliptic curves of genus 3,
based on section 11 of Prof. Dr. Michael Stoll - On the Height constant for curves of genus two; Acta Arith. 90, 183-201 (1999),
using the MAGMA Computational Algebra System. (See link below)

The code mainly expands upon existing code for genus 2 hyperelliptic curves created by Michael Stoll, 
using the functionality created and hosted by Prof. Dr. Michael Stoll on his webpage (linked below), mainly the
files G3Hyp.m and G3HypHelp.m, most of which is theoretically explained in 
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
	at the webpage of Andrew Sutherland, in the same format, but now containing a list of elementary divisors at the end, in between the "[]".
	It is the output file from running gen3databasecomputations.m, renamed to prevent overwriting.

NOTE: One curve is missing in this database in output.txt: The curve defined by
y^2 + (x^3+1)*y= -x^7-4*x^6-3*x^5+2*x^4+x^3-x^2. This is due to an internal error within MAGMA that should not
show up in the latest versions.

Links:
MAGMA Computational Algebra System:
	http://magma.maths.usyd.edu.au/magma/
MAGMA-related directory of Prof. Dr. Michael Stoll:
	http://www.mathe2.uni-bayreuth.de/stoll/magma/index.html
genus 3 hyperelliptic curves of small discriminant over Q, hosted by Andrew V. Sutherland:
	https://math.mit.edu/~drew/gce_genus3_hyperelliptic.txt

If a comment in the code references a section, theorem, lemma, etc, this refers to my Master's Thesis
