This is a formalization of an article I wrote in 2017: [Self-referential logic via self-referential circuits](http://blog.sigfpe.com/2017/07/self-referential-logic-via-self.html)

<div align="center">
<img width="256" height="134" alt="image" src="https://github.com/user-attachments/assets/22c43b31-2346-4aa8-8614-b095e1a14ac5" />
</div>

There are two ideas here:

1. a fragment of Provability Logic (letterless GL) can be thought of as describing digital electronics using AND, OR, NOT and a certain delay-latch gate.
   This means theorems about this fragment are actually theorems about these circuits. For example there's a fixed point theorem for GL that
   says we can solve (certain) equations of the form p = F(p) in a way that eliminates p and this is equivalent to saying that (certain) circuits
   with feedback loops can be redesigned to not have the loops.
2. it works both ways. Letterless GL is complete for this system so we can prove theorems of letterless GL just by observing the behaviour of these circuits.

<div align="center">
<img alt="image" src="https://github.com/user-attachments/assets/7944ef20-1249-40f7-a9d4-f09dbb851d84" />
</div>
