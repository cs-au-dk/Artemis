#ifndef S11N_NET_READLINE_HPP_INCLUDED
#define S11N_NET_READLINE_HPP_INCLUDED 1

////////////////////////////////////////////////////////////////////////
// Readline.hpp:
//
// The license this source is released under depends on whether or not
// is is linked with GNU libreadline. If so, then this code is
// released under the GNU GPL. If it is built without GNU libreadline
// support then it is released into the Public Domain.
//
// For purposes of the GPL, this library is Copyright (c) 2002-2005
// stephan beal (stephan@s11n.net).
////////////////////////////////////////////////////////////////////////

#include <string>
#include <list>
#include <iostream>


namespace readlinecpp {
        using std::string;
        using std::list;

        /**
           License: See the license text in this header file.

           Author: stephan@s11n.net

           Readline is a helper class for working with the excellent
           libreadline or libeditline libraries (using the latter's
           libreadline compatibility code).  It does not wrap all
           libreadline functionality - just that which i need ;).

           It acts as an almost-drop-in replacement for commonly-used
           libreadline functions, and can work with or without
           libreadline (using cin/cout as an inferior replacement, if
           necessary). The one notable exception is that calling
           this object's readline() function also updates the history
           list, something which the free ::readline() funcs don't
           do.

           It works with STL types instead of char *'s and handles freeing
           readline()-malloc()'d char *'s.

           Sample usage:

           string theline;
           string prompt = "prompt: ";
           bool breakout;
           Readline reader;
           do
           {
               theline = reader( prompt, breakout );
               if( breakout ) break;
               if( theline.empty() ) continue;
               if( theline == "history" )
               { // sample of implementing simple commands (map<string,functor> is prolly better)
                   cout << "History:"<<endl;
                   reader.save_history( std::cout );
                   // or: 
                   //   std::copy( reader.history().begin(), reader.history().end(), std::ostream_iterator<string>(cout,"\n") );
                   continue;
               }
           } while(1);

           There is also a simpler form of readline() which does not take a
           boolean, but cannot signal an exit via traditional means: the app must
           somehow do this (via, e.g., user typing "quit").

           Apps using this object should link with either libreadline
           or libeditline. In most Make-based build environments, that's just adding this to your
           Makefile:

             LDFLAGS += -l(editline|readline) -lncurses
           (readline/editline both use ncurses.)

           And, of course, you must have readline/editline installed on your system if
           you do that.

           Known problems:

           - The history-related functions may not reflect what is
           actually in libreadline's history, and i appologize for this. i
           haven't yet learned how to work with libhistory. This
           class pretties up the list, too, making sure there are no
           duplicates, and making it easily available for serialization
           via s11n.

           - Has hard-coded history limit of 200 at the moment, and oldest
           items are lost as the buffer fills.

           - Does not currently provide a hook into the underlying
           edit/readline implementation's special functions, like
           calling libeditline built-ins.

        */
        class Readline
        {
        public:
                Readline();
                explicit Readline( const std::string &historyFileName );
                ~Readline();

                typedef std::list<std::string> history_list;
                /**
                   Just like readline( const string &, bool & ), but
                   the bool argument is ignored.
                */
                const string & readline( const string & prompt );

                /**
                   Takes a line of input from the user and,
                   if it is not empty, calls add_history() with
                   that line. It returns the string taken from
                   the underlying user input function (see below).

                   If breakOut is set to true when this function
                   returns then the user tapped Ctrl-D, or has
                   otherwise signaled the desire to leave this place.
                   This function always sets breakOut to false by
                   default, so you need not pre-set it.

                   Note that the /exact/ behaviour of this function depends
                   on the underlying readline implementation:

                   - GNU libreadline: similar to how your Unix shell works.

                   - libeditline: a BSD-licensed implementation of libreadline,
                     but not 100% identical in usage (pretty close, though,
                     and a much more lenient license!).

                   - cin is used if support for neither libreadline nor
                   libeditline are compiled in.
                */
                const string & readline( const string & prompt, bool & breakOut );

                /**
                   Returns the last-read line. You'll probably never need this.
                */
                const string & theline();

                /**
                   Adds a line to the history. It explicitely ignores
                   empty strings.

                   See history() for important information.

                   OLD BEHAVIOUR, changed on 28 Nov 2004: If it
                   already contains an entry it adds newest entry to
                   the front and removing the old.

                   NEW BEHAVIOUR: always adds the entry to the list,
                   because this is how libreadline/editline do it
                   and tying in to their histor maps to sync it
                   with ours is more trouble than it's worth.
                */
                void add_history( const string & );

                /**
                   The list of items added via add_history() (or other
                   manipulation to this list).


                   Note that history may not match what readline
                   provides, so this list may not really be in sync with
                   what command-line editing functions will show you
                   (but it's close enough for many purposes).
                */
                history_list & history();
                const history_list & history() const;


                /**
                   Saves the history to the stream. Returns false if
                   (!os), otherwise it returns true.

                   See history() for important information.
                */
                bool save_history( std::ostream & os );
                /**
                   Saves the history to the given filename. Returns
                   false if an ofstream cannot be initialized with
                   that filename or if save_history( ostream & ) return
                   false.

                   See history() for important information.

                   If the given filename is empty, the name set in the
                   constructor, or the last call to load_history() is
                   used.
                */
                bool save_history( const std::string & = string() );

                /**
                   Duh.
                 */
                void clear_history();

                /**
                   Loads a history file (one input line = one history
                   line).  Returns false if (!is), otherwise returns
                   true.

                   Any existing history is flushed by this function.

                   See history() for important information.
                */
                bool load_history( std::istream &is );
                /**
                   Loads a history file (one input line = one history
                   line). Returns false if an ifstream cannot be
                   opened usign the given filename or if that stream
                   has a problem reading the data, otherwise returns
                   true.

                   See history() for important information.

                   If the given filename is empty, the name set in the
                   constructor, or the last call to load_history() is
                   used.

                */
                bool load_history( const std::string & );


                /**
                   Returns a string naming the internal readline implementation.

                   The exact string is not guaranteed to follow a
                   specific format, but should give the user what he
                   wants to know, provided he sees the string in
                   context.
                */
                static std::string rl_implementation_name();
        private:
                history_list m_hist;
                std::string m_preline;
                std::string m_filename; // set by load/save_history().
        };


} // namespace readlinecpp

#endif // S11N_NET_READLINE_HPP_INCLUDED
