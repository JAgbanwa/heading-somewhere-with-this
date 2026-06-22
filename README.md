## Approach 1

This project [\[1\]](https://github.com/JAgbanwa/heading-somewhere-with-this/tree/main/Potential%20directions%20with%20specific%20equations) involves running computational searches 
for solutions to a diophantine equation, which after a substitution returns rational solutions to $x^3 + y^3 + z^3 = 114$. These computational searches were run over all 8 cores of my 
MacBook M1 Pro in two waves. Wave 1 had 2/8 its 8 cores returning integer solutions with 12 hours of search and Wave 2 having 6 out of 8 cores returning integer solutions.
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

I found some relevant suggestions from this [\[conversation\]](https://chatgpt.com/c/6a393a60-b9dc-83eb-9ac3-e443f6301a0b) I'd try.
