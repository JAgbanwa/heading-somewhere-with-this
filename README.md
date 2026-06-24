This repository contains Magma and SageMath codes relevant to exploring the sums of three cubes problem largely for 114. The first two folders contain different projects I am running  which consequently this problem once we search within the right ranges. While this many files might look a bit messy, I have referenced them in a [paper](https://figshare.com/articles/preprint/Closed_form_formulas_on_the_sums_of_three_cubes_for_k_114_192_/30509981?file=61812286) which is still in progress.

## Approach 1

This project [\[1\]](https://github.com/JAgbanwa/heading-somewhere-with-this/tree/main/Potential%20directions%20with%20specific%20equations) involves running computational searches 
for solutions to a diophantine equation, which after a substitution returns rational solutions to $x^3 + y^3 + z^3 = 114$. These computational searches were run over all 8 cores of my 
MacBook M1 Pro in two waves. Wave 1 had 2/8 its 8 cores returning integer solutions with 12 hours of search and Wave 2 having 7 out of 8 cores returning integer solutions. 
The computations of Wave 2 lasted 3 days.
## Claim
The equation as in [\[1\]](https://github.com/JAgbanwa/heading-somewhere-with-this/tree/main/Potential%20directions%20with%20specific%20equations) has infinitely many integer solutions 
which translate to non-integer rational solutions to $x^3 + y^3 + z^3 = 114$ and a finite number of such integers leading to integer solutions to this problem. Such set of integers are
believed to astronomically large if any.

With access to advanced computational resources, we could target our searches for solutions of $|n|$ within ranges of $10^{20}$ to $10^{30}$ and $10^{30}$ and beyond depending on
what is the most feasible.

## Approach 2

Another approach was that, a criteria for $y^2 = (\alpha + 6n)^2 + \dfrac{36n^3 - 19}{\alpha}$ to be integer, this term $\dfrac{36n^3 - 19}{\alpha}$ has to be integer itself.
This raises the question of which congruences of $\alpha, n$ make this possible.This question is answered by running this SageMath [code](https://github.com/JAgbanwa/heading-somewhere-with-this/blob/main/code%20which%20yielded%20promising%20n%20%5Cequiv%20a%20mod%20p). This [conversation](https://claude.ai/chat/1ff2b9c1-189c-4e00-b6cb-eef422bbb169) with Claude suggests new 
congruences of $n$. The idea is to take one such congruence for $n = a(modp)=pk+a$ and we search for non-zero, integer/non-integer rational value of $k$ for which $n,\alpha,y$ from this equation $y^2 = (\alpha + 6n)^2 + \dfrac{36n^3 - 19}{\alpha}$ yields integer solutions. 

From equation 9 of this [document](https://github.com/JAgbanwa/heading-somewhere-with-this/blob/main/Efforts%20towards%20solving%20Y%5E2%20%20%3D%2036%20%5Ccdot%20x%5E3%20%2B%2036m%5E2%20%5Ccdot%20x%5E2%20%2B%2012%20m%5E3%20%5Ccdot%20x%20%2B%20m%5E4%20-%2019m%20/s3c.folder/.tex%20file),

```bash
n = 5103243448423190660018404944928000789930010683701564743465k + 1820733127217158956577191662349053768348092988705876831189
```
we substitute it into $y^2 = (\alpha + 6n)^2 + \dfrac{36n^3 - 19}{\alpha}$ to yield:

```bash
y^2 = (\alpha + 30619460690539143960110429669568004739580064102209388460790k + 10924398763302953739463149974094322610088557932235260987134)^2 +
\dfrac{4784552901717657046910952386140410566083182302650026877054752121660964103096189843657017751024472339276482878734850933847930096466248131898297321226278860780184291784358506500*k^3 +
5121092529754964411449161340146101420228399591452111284241547501882790784594208318617802044125288709834578672750549563070264585752458229541411205828336479875946370066410764700*k^2 +
1827101315213597820000110416948106607208358810083338384275965340441733187215493526894277304231141196649229390998742010658767143176530548275036317765383648969084915427119792620*k +
217290822004537567821296280762125148628451240700355478371468113838106817035358593680548375733558724611766519425198024760434348671386193909776843642323732294542277989631353665}{\alpha}
```
Given the suggestions from this [interaction](https://chatgpt.com/c/6a39771a-7d1c-83eb-9adc-6fcf0fc6ad1d), I formalized its results with the assistance of Aristotle as is found in this
[folder](https://github.com/JAgbanwa/heading-somewhere-with-this/tree/main/Efforts%20towards%20solving%20Y%5E2%20%20%3D%2036%20%5Ccdot%20x%5E3%20%2B%2036m%5E2%20%5Ccdot%20x%5E2%20%2B%2012%20m%5E3%20%5Ccdot%20x%20%2B%20m%5E4%20-%2019m%20/integer_congruences_complete_note).

Based on this suggestions, I intend to make due substitutions into the above equation and double things down in pursuits of congruences which significantly reduce the search space of this 
problem.

```bash
y'^2 = (\dfrac{12*X + 7 + 91858382071617431880331289008704014218740192306628165382370*K + 72163320144381241659684009313230332089248686136654037908714}{6})^2 +
\dfrac{129182928346376740266595714425791085284245922171550725680478307284846030783597125778739479277660753160465037725840975213894112604588699561254027673109529241064975878177679675500*K^3 + 304455689460548160236233880912897083350547440666170452919130542086637178628542126425039176952449104709441283506436896495420606480949523188380756198674086801013469086953056233300*K^2 +
239178318764536020086184553233652317243360434423076318137697542423713396688239814775749095479077892321916015880457454407344959931344023147660746987382227693505245691315194788260*K + 62632286785192847228905781564366028572624225647875692400327605775540449154612697671196453168892774671460403022303687769142467749764265263811872872296667835977971923384382049705}{36 *(12*X + 7)}
```
A final resort would be to turn to Charity Engine. I sent an email to CE pending feedback with this [code](https://github.com/JAgbanwa/heading-somewhere-with-this/tree/main/Efforts%20towards%20solving%20Y%5E2%20%20%3D%2036%20%5Ccdot%20x%5E3%20%2B%2036m%5E2%20%5Ccdot%20x%5E2%20%2B%2012%20m%5E3%20%5Ccdot%20x%20%2B%20m%5E4%20-%2019m%20/search_114)
.
