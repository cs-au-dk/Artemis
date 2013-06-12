/* Copyright (c) SRI International 2006.
   Author: Leonardo de Moura.
   Revisions: Bruno Dutertre.	 
*/
#ifndef YICES_C_H
#define YICES_C_H

#ifdef __cplusplus
extern "C" {
#endif

typedef void * yices_ast;

/**
   \defgroup capi C API

*/
/*@{*/

/**
   The current C API is not yet complete, but the basic Yices functionalities can be used.
   Dependent types, quantifiers, lambda expressions are not supported by this API right now
   but will be in the future.
 */


/** \brief Yices expressions (abstract syntax tree) */
typedef void * yices_expr;

/** \brief Yices types (abstract syntax tree) */
typedef void * yices_type;

/** 
   \brief Variable declaration 

   A declaration consists of a name and a type (such as
   <tt>x::bool</tt>).  An instance of the declaration represents the
   term <tt>x</tt>. Instances are also called name
   expressions. Instances can be created using
   #yices_mk_bool_var_from_decl or #yices_mk_var_from_decl.
*/
typedef void * yices_var_decl;

/** 
   \brief Yices context.

   A context stores a collection of declarations and assertions.

 */
typedef void * yices_context;

/**
   \brief Assertion index, to identify retractable assertions.  
 */
typedef int assertion_id;

/**
  \brief Model.

  A model assigns constant values to variables defined in a context.
  The context must be known to be consistent for a model to be available.
  The model is constructed by calling #yices_check (or its relatives) then
  #yices_get_model.
*/
typedef void * yices_model;

/**
   \brief Iterator for scanning the boolean variables.
*/
typedef void * yices_var_decl_iterator;


/** 
  \brief Extended booleans: to represent the value of literals in the context 
*/
typedef enum { l_false=-1, l_undef, l_true } lbool;



/**
   \brief Set the verbosity level. 
 */
void yices_set_verbosity(int l);

/**
   \brief Return the yices version number.
*/
char * yices_version();

/**

   \brief Set the maximum number of conflicts that are allowed in a maxsat iteration.

   If the maximum is reached, then "unknown" (i.e., l_undef) is returned by maxsat.
 */
void yices_set_max_num_conflicts_in_maxsat_iteration(unsigned n);

/**
   \brief Force Yices to type check expressions when they are asserted (default = false).
 */
void yices_enable_type_checker(int flag);

/**
   \brief Set the maximum number of iterations in the MaxSAT algorithm.

   If the maximum is reached, then "unknown" (i.e., l_undef) is returned by maxsat.
 */
void yices_set_max_num_iterations_in_maxsat (unsigned n);

/**
   \brief Set the initial cost for a maxsat problem.
 */
void yices_set_maxsat_initial_cost(long long c);

/**
   \brief Inform yices that only arithmetic theory is going to be used.

   This flag usually improves performance (default = false).
 */
void yices_set_arith_only(int flag);

/**
   \brief Enable a log file that will store the assertions, checks, decls, etc.

   If the log file is already open, then nothing happens.
 */
void yices_enable_log_file(char * file_name);

/**
   \brief Create a logical context.
 */
yices_context yices_mk_context();

/**
   \brief Delete the given logical context.
	 
   \sa yices_mk_context
 */
void yices_del_context(yices_context ctx);

/**
   \brief Reset the given logical context. 
 */
void yices_reset(yices_context ctx);

/**
   \brief Display the internal representation of the given logical context on <tt>stderr</tt>. 

   This function is mostly for debugging.
 */
void yices_dump_context(yices_context ctx);

/**
   \brief Create a backtracking point in the given logical context.
   
   The logical context can be viewed as a stack of contexts.
   The scope level is the number of elements on this stack. The stack
   of contexts is simulated using trail (undo) stacks.
 */
void yices_push(yices_context ctx);

/**
   \brief Backtrack.

   Restores the context from the top of the stack, and pops it off the
   stack.  Any changes to the logical context (by #yices_assert or
   other functions) between the matching #yices_push and \c yices_pop
   operators are flushed, and the context is completely restored to
   what it was right before the #yices_push.
   
   \sa yices_push
 */
void yices_pop(yices_context ctx);

/**
   \brief Assert a constraint in the logical context.
	 
   After one assertion, the logical context may become inconsistent.
   The method #yices_inconsistent may be used to check that.       
 */
void yices_assert(yices_context ctx, yices_expr expr);

/**
   \brief Assert a constraint in the logical context with weight \c w.
	 
   \returns An id that can be used to retract the constraint.

   \sa yices_retract
*/
assertion_id yices_assert_weighted(yices_context ctx, yices_expr expr, long long w);

/**
   \brief Assert a constraint that can be later retracted.

   \returns An id that can be used to retract the constraint.

   This is similar to #yices_assert_weighted, but the weight is considered to be infinite.

   \sa yices_retract
*/
assertion_id yices_assert_retractable(yices_context ctx, yices_expr expr);

/**
   \brief Retract a retractable or weighted constraint.
   
   \sa yices_assert_weighted
   \sa yices_assert_retractable
*/
void yices_retract(yices_context ctx, assertion_id id);

/**
   \brief Return 1 if the logical context is known to be inconsistent.
*/
int yices_inconsistent(yices_context ctx);

/**
   \brief Check if the logical context is satisfiable. 

   - \c l_true means the context is satisfiable
   - \c l_false means it is unsatisfiable
   - \c l_undef means it was not possible to decide due to an incompleteness.

   If the context is satisfiable, then #yices_get_model can be used to obtain a model.

   \warning This method ignore the weights associated with the constraints.  
 */
lbool yices_check(yices_context ctx);


/**
  \brief Search for a model of the constraints asserted in \c ctx
  and compute its cost. 

  If \c random is non-zero, then random search is used,
  otherwise, the default decision heuristic is used.

  If there are no weighted constaints in \c ctx, then this function is the same as #yices_check.

  Otherwise, it searches for a model that satisfies all the
  non-weighted constraints but not necessarily the weighted
  constraints. The function returns \c l_true if such a model is
  found, and the model can be obtained using #yices_get_model.  The
  cost of this model is the sum of the weights of the unsatisfied
  weighted constraints.

  The function returns \c l_false if it cannot find such a model.

  The function may also return \c l_undef, if the context contains
  formulas for which yices is incomplete (e.g., quantifiers). Do not
  use the model in this case.
*/
lbool yices_find_weighted_model(yices_context ctx, int random);


/**
   \brief Evaluate a formula in a model.

   Model \c m can be obtained via #yices_get_model, after a call to #yices_check,
   #yices_max_sat, or #yices_find_weighted_model

   - \c l_true means the formula is true in the model
   - \c l_false means the formula is false in the model
   - \c l_undef means the model does not have enough information.
        typically this is due to a function application, e.g., 
	the model defines (f 1) and (f 2), but the formula references (f 3)
*/
lbool yices_evaluate_in_model(yices_model m, yices_expr e);  


/**
   \brief Compute the maximal satisfying assignment for the asserted
   weighted constraints.

   - \c l_true means the maximal satisfying assignment was found
   - \c l_false means it is unsatisfiable (this may happen if the context has 
   unweighted constraints)
   - \c l_undef means it was not possible to decide due to an incompleteness.
   If the result is \c l_true, then #yices_get_model can be used to obtain a model.
			 
   \sa yices_assert_weighted
*/
lbool yices_max_sat(yices_context ctx);

/**
   \brief Similar to yices_max_sat, but start looking for models with cost
   less than of equal to \c max_cost.

   \return l_false if such a model doesn't exist.
 */
lbool yices_max_sat_cost_leq(yices_context c, long long max_cost);



/**
   \brief Return a model for a satisfiable logical context.

   \warning The should be only called if #yices_check or #yices_max_sat 
   returned \c l_true or \c l_undef.

   Return 0 if a model is not available.
   Calls to functions which modify the context invalidate the model.
 */
yices_model yices_get_model(yices_context ctx);



/**
   \brief Get the size of the unsat core

   The unsat core is constructed after a call to #yices_check 
   if the context is found unsatisfiable. It's an unsatisfiable 
   subset of the retractable assertions (represented as an array
   of \c assertion_ids). This function returns the size of that 
   set.

   Return 0 if there's no unsat core.

   \sa yices_get_unsat_core
**/
unsigned yices_get_unsat_core_size(yices_context ctx);



/**
   \brief Copy the unsat core into array a

   \warning a must be large enough to store the core 
   (check the size first using #yices_get_unsat_core_size)

   Each element in a is the id of a retractable assertion 

   Return the number of elements copied into a (which is 
   equal to the unsat core size as returned by 
   #yices_get_unsat_core_size)

   \sa yices_assert_retractable
   \sa yices_get_unsat_core_size

**/
unsigned yices_get_unsat_core(yices_context ctx, assertion_id a[]);    



/**
   \brief Return the assignment for the variable \c v. 

   The result is \c l_undef if the value of \c v is a "don't care".

   \warning \c v must be the declaration of a boolean variable

   \sa yices_get_int_value
   \sa yices_get_arith_value
   \sa yices_get_double_value
 */
lbool yices_get_value(yices_model m, yices_var_decl v);


/**
   \brief Get the integer value assigned to variable \c v in model \c m

   The value is stored in <tt>* value<tt>. Returns 1 on success.

   A return code of 0 indicates one of the following errors:
   - \c v is not a proper declaration or not the declaration of a numerical variable
   - \c v has no value assigned in model m (typically, this means that v does not 
   occur in the asserted constraints)
   - \c v has a value that cannot be converted to <tt>long</tt>, because
   it is rational or too big 

   \sa yices_get_value
   \sa yices_get_arith_value
   \sa yices_get_double_value
*/
int yices_get_int_value(yices_model m, yices_var_decl d, long *value);


/**
   \brief Get the rational value assigned to variable \c v in model \c m

   The numerator is stored in <tt>* num</tt> and the denominator 
   in <tt>* den</tt>. Returns 1 on success.

   A return code of 0 indicates one of the following errors:
   - \c v is not a proper declaration or not the declaration of a numerical variable
   - \c v has no value assigned in model m (typically, this means that v does not 
   occur in the asserted constraints)
   - \c v has a value that cannot be converted to <tt>long/long</tt>, 
   because the numerator or the denominator is too big

   \sa yices_get_value
   \sa yices_get_int_value
   \sa yices_get_double_value
*/
int yices_get_arith_value(yices_model m, yices_var_decl d, long *num, long *den);


/**
   \brief Convert the value assigned to variable \c v in model \c m to a floating 
   point number. 

   The value is stored in <tt>* value<tt>. Returns 1 on success.

   A return code of 0 indicates one of the following errors:
   - \c v is not a proper declaration or not the declaration of a numerical variable
   - \c v has no value assigned in model m (typically, this means that v does not 
   occur in the asserted constraints)

   \sa yices_get_value
   \sa yices_get_int_value
   \sa yices_get_arith_value
*/
int yices_get_double_value(yices_model m, yices_var_decl d, double *value);


/**
   \brief Convert the value assigned to variable \c v in model \c m to a GMP rational (\c mpq_t)  

   Return 1 on success.

   A return code of 0 indicates one of the following errors:
   - \c v is not a proper declaration or not the declaration of a numerical variable
   - \c v has no value assigned in model m (typically, this means that v does not 
   occur in the asserted constraints)

   \warning 
   - For this function to be declared properly, put \#include <gmp.h>
   before \#include <yices_c.h> in your code. If you don't need GMP numbers, don't include <gmp.h>.
   - The \c mpq_t object \c value must be initialized first, by calling GMP's <tt>mpq_init</tt> function.
   (Check the GNU MP documentation).
  

   \sa yices_get_mpz_value.
*/
#ifdef __GMP_H__
int yices_get_mpq_value(yices_model m, yices_var_decl d, mpq_t value);
#endif

/**
   \brief Convert the value assigned to variable \c v in model \c m to a GMP integer (\c mpz_t)

   Return 1 on success

   A return code of 0 indicates one of the following errors:
   - \c v is not a proper declaration or not the declaration of a numerical variable
   - \c v has no value assigned in model m (typically, this means that v does not 
   occur in the asserted constraints)
   - \c the value assigned to v is not an integer.

   \warning 
   - For this function to be declared properly, put <tt>\#include <gmp.h></tt>
   before <tt>\#include <yices_c.h></tt> in your code. If you don't need GMP numbers, don't include <gmp.h>.
   - The \c mpz_t object \c value must be initialized first, by calling GMP's <tt>mpz_init</tt> function
   or its variants. (Check the GNU MP documentation).

   \sa yices_get_mpq_value.
*/
#ifdef __GMP_H__
int yices_get_mpz_value(yices_model m, yices_var_decl d, mpz_t value);
#endif



/**
   \brief Get the bitvector constant assigned to a variable v in model m.   
  
   The value stored in array \c bv: <tt>bv[0]</tt> is the low-order
   bit and <tt>bv[n - 1]</tt> is the high-order bit. 

   - \c n should be the size of the bitvector variable v.  Otherwise, if
   - \c n is smaller than \c v's size, the n lower-order bits of v
   are returned. If \c n is larger than \c v's size then the extra
   high-order bits are set to 0.

   The return code is 0 if an error occurs, 1 otherwise. Possible errors are:
   - \c d is not the declaration of a bitvector variable.
   - \c d is not assigned a value in model m   
   
*/
int yices_get_bitvector_value(yices_model m, yices_var_decl d, unsigned n, int bv[]);


/**
   \brief Return 1 (0) if the assertion of the given \c id is satisfied (not
   satisfied) in the model \c m.

   This function is only useful for assertion ids obtained using #yices_assert_weighted,
   and #yices_max_sat was used to build the model. That is the only scenario where an
   assertion may not be satisfied in a model produced by yices.
 */
int yices_get_assertion_value(yices_model m, assertion_id id);


/**
   \brief Display the given model in the standard output.
 */
void yices_display_model(yices_model m);


/**
   \brief Return the cost of model \c m. 

   The cost is the sum of the weights of unsatisfied constraints.
	 
   \warning The model cost is computed automatically by #yices_max_sat but 
   not by #yices_check. If #yices_check returns \c l_true (or \c l_undef),
   you can call #yices_compute_model_cost to compute the cost explicitly.
 */
long long yices_get_cost(yices_model m);


/**
   \brief Return the cost of the model m, converted to a double-precision 
   floating point number.
*/
double yices_get_cost_as_double(yices_model m);


/**
   \brief Return an expression representing \c true.
 */
yices_expr yices_mk_true(yices_context ctx);


/**
   \brief Return an expression representing \c false.
 */
yices_expr yices_mk_false(yices_context ctx);


/**
   \brief Return a name expression for the given variable name. 

   <tt>yices_mk_bool_var(c, n1) == yices_mk_bool_var(c, n2)</tt> when <tt>strcmp(n1, n2) == 0</tt>.
	 
   \sa yices_mk_bool_var_decl
   \sa yices_mk_fresh_bool_var
   \sa yices_mk_bool_var_from_decl
 */
yices_expr yices_mk_bool_var(yices_context ctx, char * name);


/**
   \brief Return a fresh boolean variable.
 */
yices_expr yices_mk_fresh_bool_var(yices_context ctx);


/**
   \brief Return the variable declaration object associated with the given name expression.

   \warning \c e must be a name expression created using methods such
   as: #yices_mk_bool_var, #yices_mk_fresh_bool_var, or #yices_mk_bool_var_from_decl.
 */
yices_var_decl yices_get_var_decl(yices_expr e);

/**
   \brief Return a new boolean variable declaration. 
   
   It is an error to create two variables with the same name.
 */
yices_var_decl yices_mk_bool_var_decl(yices_context ctx, char * name);

/**
   \brief Return a name of a variable declaration.
 */
char * yices_get_var_decl_name(yices_var_decl d);

/**
   \brief Return a name expression (instance) using the given variable declaration.
 */
yices_expr yices_mk_bool_var_from_decl(yices_context ctx, yices_var_decl d);

/**
   \brief Return an expression representing the \c or of the given arguments.

   \c n is the number of elements in the array \c args.
	 
   \warning \c n must be greater than zero.
 */
yices_expr yices_mk_or(yices_context ctx, yices_expr args[], unsigned n);

/**
   \brief Return an expression representing the \c and of the given arguments.

   \c n is the number of elements in the array \c args.

   \warning \c n must be greater than zero.
 */
yices_expr yices_mk_and(yices_context ctx, yices_expr args[], unsigned n);

/**
   \brief Return an expression representing <tt>a1 = a2</tt>.
 */
yices_expr yices_mk_eq(yices_context ctx, yices_expr a1, yices_expr a2);

/**
   \brief Return an expression representing <tt>a1 /= a2</tt>.
 */
yices_expr yices_mk_diseq(yices_context ctx, yices_expr a1, yices_expr a2);

/**
   \brief Return an expression representing <tt>(if c t e)</tt>.
 */
yices_expr yices_mk_ite(yices_context ctx, yices_expr c, yices_expr t, yices_expr e);

/**
   \brief Return an expression representing <tt>(not a)</tt>.
 */
yices_expr yices_mk_not(yices_context ctx, yices_expr a);

/**
   \brief Create an iterator that can be used to traverse the boolean variables (var_decl objects) in the 
   given logical context. 

   An iterator is particulary useful when we want to extract the assignment
   (model) produced by the #yices_check command.

   Example:
   \code
   yices_context ctx = yices_mk_context();
   ...
   if (yices_check(ctx) == l_true) {
      yices_var_decl_iterator it = yices_create_var_decl_iterator(ctx);
      yices_model m              = yices_get_model(ctx);
      while (yices_iterator_has_next(it)) {
         yices_var_decl d         = yices_iterator_next(it);
	 char *         val;
	 switch(yices_get_value(m, d)) {
	 case l_true: 
  	    val = "true"; 
	    break;
	 case l_false: 
	    val = "false";
	    break;
	 case l_undef: 
	    val = "unknown"; 
	    break;
	 }
	 printf("%s = %s\n", yices_get_var_decl_name(d), val);
      }
      yices_del_iterator(it);
   }
   \endcode
	 	 
   \sa yices_iterator_has_next
   \sa yices_iterator_next
   \sa yices_iterator_reset
 */
yices_var_decl_iterator yices_create_var_decl_iterator(yices_context c);

/**
   \brief Return 1 if the iterator \c it still has elements to be iterated.
   Return 0 otherwise.
	 
   \sa yices_iterator_next
   \sa yices_create_var_decl_iterator
 */
int yices_iterator_has_next(yices_var_decl_iterator it);

/**
   \brief Return the next variable, and move the iterator.

   \sa yices_iterator_has_next
   \sa yices_create_var_decl_iterator
 */
yices_var_decl yices_iterator_next(yices_var_decl_iterator it);

/**
   \brief Reset the given iterator, that is, move it back to the first element.
 */
void yices_iterator_reset(yices_var_decl_iterator it);

/**
   \brief Delete an iterator created with #yices_create_var_decl_iterator.
 */
void yices_del_iterator(yices_var_decl_iterator it);

/**
   \brief Return the type associated with the given name. If the type
   does not exist, a new uninterpreted type is created.

   \remark number, real, int, nat, bool, any are builtin types.
 */
yices_type yices_mk_type(yices_context ctx, char * name);

/**
   \brief Return a function type <tt>(-> d1 ... dn r)</tt>.
 */
yices_type yices_mk_function_type(yices_context ctx, yices_type domain[], 
				  unsigned domain_size, yices_type range);



/**
   \brief Returns the bitvector type (bv[size]).
   
   Size must be positive.
*/
yices_type yices_mk_bitvector_type(yices_context ctx, unsigned size);


/**
  \brief Constructs the tuple type (arg[0], ..., arg[size-1]).
*/
yices_type yices_mk_tuple_type(yices_context ctx, yices_type * args[], unsigned size);


/**
   \brief Return a new (global) variable declaration. It is an error to create two variables
   with the same name.
*/
yices_var_decl yices_mk_var_decl(yices_context ctx, char * name, yices_type ty);

/**
   \brief Return a variable declaration associated with the given name. 

   Return 0 if there is no variable declaration associated with the given name.
*/
yices_var_decl yices_get_var_decl_from_name(yices_context ctx, char * name);

/**
   \brief Return a name expression (instance) using the given variable declaration.
*/
yices_expr yices_mk_var_from_decl(yices_context ctx, yices_var_decl d);

/**
   \brief Return a function application term <tt>(f t1 ... tn)</tt>.

   The type of \c f must be a function-type, and its arity must
   be equal to the number of arguments.
 */
yices_expr yices_mk_app(yices_context ctx, yices_expr f, yices_expr args[], unsigned n);


/**
   \brief Return an expression representing the given integer.
 */
yices_expr yices_mk_num(yices_context ctx, int n);

/**
   \brief Return an expression representing the number provided in ASCII format.
 */
yices_expr yices_mk_num_from_string(yices_context ctx, char * n);


/**
  \brief Construct a numerical expression form a GMP integer

  \warning
  - You must include <gmp.h> before <yices_c.h> for this function to be available.
  - If you don't need GMP numbers, don't include <gmp.h>

  \sa yices_mk_num_from_mpq
*/
#ifdef __GMP_H__
yices_expr yices_mk_num_from_mpz(yices_context ctx, const mpz_t z);
#endif


/**
  \brief Construct a numerical expression form a GMP rational

  q must be canonicalized (see GMP documentation).

  \warning
  - You must include <gmp.h> before <yices_c.h> for this function to be available.
  - If you don't need GMP numbers, don't include <gmp.h>

  \sa yices_mk_num_from_mpq
*/
#ifdef __GMP_H__
yices_expr yices_mk_num_from_mpq(yices_context ctx, const mpq_t q);
#endif


/**
   \brief Return an expression representing <tt>args[0] + ... + args[n-1]</tt>.

   \c n is the number of elements in the array \c args.
	 
   \warning \c n must be greater than zero.
 */
yices_expr yices_mk_sum(yices_context ctx, yices_expr args[], unsigned n);

/**
   \brief Return an expression representing <tt>args[0] - ... - args[n-1]</tt>.

   \c n is the number of elements in the array \c args.
	 
   \warning \c n must be greater than zero.
 */
yices_expr yices_mk_sub(yices_context ctx, yices_expr args[], unsigned n);

/**
   \brief Return an expression representing <tt>args[0] * ... * args[n-1]</tt>.

   \c n is the number of elements in the array \c args.
	 
   \warning \c n must be greater than zero.
 */
yices_expr yices_mk_mul(yices_context ctx, yices_expr args[], unsigned n);

/**
   \brief Return an expression representing <tt>a1 < a2</tt>.
 */
yices_expr yices_mk_lt(yices_context ctx, yices_expr a1, yices_expr a2);

/**
   \brief Return an expression representing <tt>a1 <= a2</tt>.
 */
yices_expr yices_mk_le(yices_context ctx, yices_expr a1, yices_expr a2);

/**
   \brief Return an expression representing <tt>a1 > a2</tt>.
 */
yices_expr yices_mk_gt(yices_context ctx, yices_expr a1, yices_expr a2);

/**
   \brief Return an expression representing <tt>a1 >= a2</tt>.
 */
yices_expr yices_mk_ge(yices_context ctx, yices_expr a1, yices_expr a2);




/**
   \brief Create a bit vector constant of \c size bits and of the given \c value

   \c size must be positive
*/
yices_expr yices_mk_bv_constant(yices_context ctx, unsigned size, unsigned long value);


/**
   \brief Create a bit vector constant from an array

   \c size must be positive
   \c bv must be an array of \c size elements

   bit \c i of the bitvector is set to 0 if <tt>bv[i] = 0</tt> and to 1 if <tt>bv[i] != 0</tt>
*/
yices_expr yices_mk_bv_constant_from_array(yices_context ctx, unsigned size, int bv[]);


/**
   \brief Bitvector addition

   \c a1 and \c a2 must be bitvector expression of same size.
*/
yices_expr yices_mk_bv_add(yices_context ctx, yices_expr a1, yices_expr a2);

/**
   \brief Bitvector subtraction

   \c a1 and \c a2 must be bitvector expression of same size.
*/
yices_expr yices_mk_bv_sub(yices_context ctx, yices_expr a1, yices_expr a2);

/**
   \brief Bitvector multiplication

   \c a1 and \c a2 must be bitvector expression of same size. The result is
   truncated to that size too. E.g., multiplication of two 8-bit vectors
   gives an 8-bit result.
*/
yices_expr yices_mk_bv_mul(yices_context ctx, yices_expr a1, yices_expr a2);

/**
   \brief Bitvector opposite

   \c a1 must be bitvector expression. The result is (- \c a1). 
*/
yices_expr yices_mk_bv_minus(yices_context ctx, yices_expr a1);

/**
  \brief Bitvector concatenation 

  \c a1 and \c a2 must be two bitvector expressions. \c a1 is the left 
  part of the result and \c a2 the right part. 

  Assuming \c a1 and \c a2 have \c n1 and \c n2 bits, respectively,
  then the result is a bitvector \c concat of size \c n1 + \c n2.  Bit
  0 of \c concat is bit 0 of \c a2 and bit \c n2 of \c concat is bit 0
  of \c a1.
*/
yices_expr yices_mk_bv_concat(yices_context ctx, yices_expr a1, yices_expr a2);


/**
  \brief Bitwise and

  \c a1 and \c a2 must be bitvector expression of same size.
*/
yices_expr yices_mk_bv_and(yices_context ctx, yices_expr a1, yices_expr a2);

/**
  \brief Bitwise or

  \c a1 and \c a2 must be bitvector expression of same size.
*/
yices_expr yices_mk_bv_or(yices_context ctx, yices_expr a1, yices_expr a2);

/**
  \brief Bitwise exclusive or

  \c a1 and \c a2 must be bitvector expression of same size.
*/
yices_expr yices_mk_bv_xor(yices_context ctx, yices_expr a1, yices_expr a2);

/**
  \brief Bitwise negation
*/
yices_expr yices_mk_bv_not(yices_context ctx, yices_expr a1);


/** 
  \brief Bitvector extraction

  \c a must a bitvector expression of size \c n with \c begin < \c end < \c n.
  The result is the subvector \c a[begin .. end]
*/ 
yices_expr yices_mk_bv_extract(yices_context ctx, unsigned end, unsigned begin, yices_expr a);

/**
  \brief Sign extension

  Append \c n times the most-significant bit of \a to the left of \c a
*/
yices_expr yices_mk_bv_sign_extend(yices_context ctx, yices_expr a, unsigned n);


/** 
  \brief Left shift by \c n bits, padding with zeros
*/
yices_expr yices_mk_bv_shift_left0(yices_context ctx, yices_expr a, unsigned n);


/** 
  \brief Left shift by \c n bits, padding with ones
*/
yices_expr yices_mk_bv_shift_left1(yices_context ctx, yices_expr a, unsigned n);

/** 
  \brief Right shift by \c n bits, padding with zeros
*/
yices_expr yices_mk_bv_shift_right0(yices_context ctx, yices_expr a, unsigned n);


/** 
  \brief Right shift by \c n bits, padding with ones
*/
yices_expr yices_mk_bv_shift_right1(yices_context ctx, yices_expr a, unsigned n);


/**
  \brief Unsigned comparison: (\c a1 < \c a2)

  \c a1 and \c a2 must be bitvector expression of same size.
*/
yices_expr yices_mk_bv_lt(yices_context ctx, yices_expr a1, yices_expr a2);

/**
  \brief Unsigned comparison: (\c a1 <= \c a2)

  \c a1 and \c a2 must be bitvector expression of same size.
*/
yices_expr yices_mk_bv_le(yices_context ctx, yices_expr a1, yices_expr a2);


/**
  \brief Unsigned comparison: (\c a1 > \c a2)

  \c a1 and \c a2 must be bitvector expression of same size.
*/
yices_expr yices_mk_bv_gt(yices_context ctx, yices_expr a1, yices_expr a2);


/**
  \brief Unsigned comparison: (\c a1 >= \c a2)

  \c a1 and \c a2 must be bitvector expression of same size.
*/
yices_expr yices_mk_bv_ge(yices_context ctx, yices_expr a1, yices_expr a2);


/**
  \brief Signed comparison: (\c a1 < \c a2)

  \c a1 and \c a2 must be bitvector expression of same size.
*/
yices_expr yices_mk_bv_slt(yices_context ctx, yices_expr a1, yices_expr a2);

/**
  \brief Signed comparison: (\c a1 <= \c a2)

  \c a1 and \c a2 must be bitvector expression of same size.
*/
yices_expr yices_mk_bv_sle(yices_context ctx, yices_expr a1, yices_expr a2);


/**
  \brief Signed comparison: (\c a1 > \c a2)

  \c a1 and \c a2 must be bitvector expression of same size.
*/
yices_expr yices_mk_bv_sgt(yices_context ctx, yices_expr a1, yices_expr a2);


/**
  \brief Signed comparison: (\c a1 >= \c a2)

  \c a1 and \c a2 must be bitvector expression of same size.
*/
yices_expr yices_mk_bv_sge(yices_context ctx, yices_expr a1, yices_expr a2);


/**
   \brief Pretty print the given expression in the standard output.
*/
void yices_pp_expr(yices_expr e);

#ifdef __cplusplus
} /* end of extern "C" */
#endif


/*@}*/
#endif /* YICES_C_H */
