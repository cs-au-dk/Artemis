// Copyright (c) SRI International 2006.
// Author: Leonardo de Moura
#ifndef YICESL_C_H
#define YICESL_C_H

#ifdef __cplusplus
extern "C" {
#endif

typedef void * yicesl_context;

/**
   \defgroup capil C API Lite
*/
/*@{*/
/**
   \brief Set the verbosity level. 
 */
void yicesl_set_verbosity(int l);

/**
   \brief Return the yices version number.
 */
char * yicesl_version();

/**
   \brief Force Yices to type check expressions when they are asserted (default = false).
 */
void yicesl_enable_type_checker(int flag);

/**
   \brief Enable a log file that will store the assertions, checks, decls, etc.
   If the log file is already open, then nothing happens.
 */
void yicesl_enable_log_file(char * file_name);

/**
   \brief Create a logical context.
 */
yicesl_context yicesl_mk_context();


/**
   \brief Delete the given logical context.
   
   \sa yicesl_mk_context
 */
void yicesl_del_context(yicesl_context ctx);

/**
   \brief Process the given command in the given logical context.
   The command must use Yices input language.
	 
   \return a non-zero value if success, and 0 if command failed.
   Commands yicesl_get_last_error_message can be used to retrieve
   the error message.
 */
int yicesl_read(yicesl_context ctx, char * cmd);

/**
   \brief Return true if the given logical context is inconsistent.
 */
int yicesl_inconsistent(yicesl_context ctx);

/**
   \brief Return the last error message produced by the logical context.
 */
char * yicesl_get_last_error_message();

/**
   \brief Set the file that will store the output produced by yices (e.g., models).
   The default behavior is to send the output to standard output.
 */
void yicesl_set_output_file(char * file_name);

/*@}*/
#ifdef __cplusplus
} /* end of extern "C" */
#endif


#endif /* YICESL_C_H */
