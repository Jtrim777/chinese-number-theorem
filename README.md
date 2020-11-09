# Chinese Remainder Theorem

## §1. General Problem Area
### §1.1. The Chinese Remainder Theorem
In Number Theory, a linear equation of the form $ax \equiv b(\mod m)$ will have a solution for $x$ if and only if the greatest common denominator ($d$) of $a$ and $m$ divides $b$. In the cases where $d | b$, $x$ can be represented as a set which is given by the residue class modulo $m/d$. In the case, however, that there are multiple linear congruences within a system who have different modulo $m$ and simultaneously solve for $x$, a theorem known as the Chinese Remainder Theorem can be used to determine the solution to the system. This theorem states that if the values $m_1, m_2, ... m_k$ are pairwise co-prime positive integers and $a_1, a_2, ... a_k$ are arbitrary integers within a linear system that is written in the form  \
$x \equiv a_1(\mod m_1)$\
$x \equiv a_2(\mod m_2)$\
..  ... ....\
$x \equiv a_k(\mod m_k)$\
then the linear system has an integral solution $x$, which is unique in the range $[0, \prod^k_{i=1}m_i)$.  \
In its simplest definition, the Chinese Remainder Theorem is a theorem that given a system of linear congruence with co-prime moduli, returns a unique solution. It is a clean and efficient way to solve several different problems in the subject of Number Theory.
### 1.2. Theorem Implementation
The process of implementing the Chinese Remainder Theorem to solve a collection of linear congruence with co-prime moduli is detailed as such:  \
1) First, the congruences are ordered by ascending value of the moduli. The last congruence is then rewritten from the form $x \equiv a_k(\mod m_k)$ to the equation $x = m_kb_k+a_k$ for some positive integer $b_k$
