#print "Chapter 10. Type Classes

We've seen that Lean's elaborator provides helpful automation, filling in information 
that is tedious to enter by hand. In this section we'll explore a simple but powerful 
technical device known as *type class inference*, which provides yet another mechanism 
for the elaborator to supply missing information.

*Type classes* originated with *Haskell*. In that context, type classes are often used 
to associate operations, like a canonical addition or multiplication, to a data type. 
This and other original uses carry over, but, as we will see, the realm of interactive 
theorem proving raises even more possibilities for their use."


#print "Section 10.1. Type Classes and Instances

Any family of types can be marked as a *type class*. We can then declare particular 
elements of a type class to be *instances*. These provide hints to the elaborator: 
any time the elaborator is looking for an element of a type class, it can consult a 
table of declared instances to find a suitable element.

More precisely, there are three steps involved:

1. declare a family of inductive types to be a type class;
2. declare instances of the type class;
3. mark some implicit arguments with square brackets instead of curly brackets 
   to tell the elaborator to infer these arguments using the type class mechanism.

We start with an example scenario. 

Many theorems hold under the additional assumption that a type is inhabited, which 
is to say, it has at least one element. For example, if `α` is a type, then
`∃ x : α, x = x` holds iff `α` is inhabited. 

Similarly, we often want a definition to return a default element in a 'corner case.' 
For example, `head l` should be of type `α` when `l : list α`, but then we are faced 
with the problem that `head l` needs to return an 'arbitrary' element of type `α` when
`l` happens to be the empty list, `nil`.

The std lib defines the type class `inhabited : Type → Type` to enable type class 
inference to infer a 'default' or 'arbitrary' element of an inhabited type."

namespace Sec_10_1
-- First, we declare an appropriate class:



end Sec_10_1


#print "==========================================="
#print "Section 10.2. Chaining Instances"
#print " "

namespace Sec_10_2

end Sec_10_2


#print "==========================================="
#print "Section 10.3. Decidable Propositions"
#print " "

namespace Sec_10_3

end Sec_10_3


#print "==========================================="
#print "Section 10.4. Overloading with Type Classes"
#print " "

namespace Sec_10_4

end Sec_10_4


#print "==========================================="
#print "Section 10.5. Managing Type Class Inference"
#print " "

namespace Sec_10_5

end Sec_10_5


#print "==========================================="
#print "Section 10.6. Coercions using Type Classes"
#print " "

namespace Sec_10_6

end Sec_10_6


