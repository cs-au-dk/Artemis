#include <iostream> // so we can output a warning if no readline is compiled in, and for ^C
#include <algorithm> // find()
#include <iterator> // for use with std::copy()
#include <fstream> // ofstream
#include <vector>
#include <map>

#include <stdio.h> // stdout, stderr, stdin

////////////////////////////////////////////////////////////////////////
// Readline.cpp:
//
// The license this source is released under depends on whether or not
// is is linked with GNU libreadline. If so, then this code is
// released under the GNU GPL. If it is built without GNU libreadline
// support then it is released into the Public Domain.
//
// For purposes of the GPL, this library is Copyright (c) 2002-2005
// stephan beal (stephan@s11n.net).
////////////////////////////////////////////////////////////////////////


#include "Readline.hpp"

#include "Readline_config.hpp" // tells us whether or not to use libreadline/editline

#define CERR std::cerr << __FILE__<<":"<<__LINE__<<": "

#if LIBREADLINECPP_USE_GENUINE_LIBEDIT
#    define USE_EDIT 1
#    include <editline/readline.h>
//#    include <editline/histedit.h>
#elif LIBREADLINECPP_USE_LIBEDITLINE
#    define USE_EDIT 1
#    include <editline/editline.h>
#    include <editline/el.h>
#elif LIBREADLINECPP_USE_LIBREADLINE
#    define USE_EDIT 1
#    include <readline/readline.h>
#    include <readline/history.h>
#else
#  define USE_EDIT 0
#endif
// maintenance note: USE_EDIT blocks only work
// for APIs which are compatible between GNU readline
// and libeditline.


#define MAX_HISTORY_SIZE 500


#define READLINE_USE_SIGNALS 1
// ^^^ set to zero on cygwin boxes.
#if READLINE_USE_SIGNALS
#  include <stdlib.h> // atexit()
#  include <signal.h> // signal()
#  include <setjmp.h> // longjmp()
#endif


#if READLINE_USE_SIGNALS
        sigjmp_buf Readline_ctrl_c_jmp_buffer;
        // anyone know how to get readline to behave like it does in bash when a ctrl-c is pressed?
        void Readline_SIGINT(int)
        {
#if LIBREADLINECPP_USE_LIBREADLINE
                rl_free_line_state();
                rl_cleanup_after_signal();
                rl_reset_after_signal();
#endif // LIBREADLINECPP_USE_LIBREADLINE
                std::cout << "^C" << std::endl; // this really shouldn't be here, but i find it useful.
                siglongjmp( Readline_ctrl_c_jmp_buffer, 1 ); // my first longjmp() :)
        }
#endif // READLINE_USE_SIGNALS

namespace readlinecpp {


//#if (LIBREADLINECPP_USE_LIBEDITLINE || LIBREADLINECPP_USE_GENUINE_LIBEDIT)
#if (LIBREADLINECPP_USE_LIBEDITLINE)

        std::string m_prompt; // huge kludge to accomodate libeditline
        const char * readline_prompt(EditLine *)
        {
                return m_prompt.c_str();
        }

        /**
           el_holder maps Readline objects to EditLine structures. It
           is only compiled in if libeditline support is. It is used
           to keep from having an EntryLine member in Readline, thus
           keeping the header (and clients) ignorant of this detail.
        */
        struct el_holder
        {
                struct eldata
                {
                        EditLine * el;
                        History * hist;
                        HistEvent hevt;
                        eldata() : el(0),hist(0)
                        {
                        }
                        ~eldata()
                        {
                        }
                };

                /**
                   Don't use - we're currently sharing the el_readline_el().

                   Calling this initializes (if necessary) an eldata object for r.
                   The client must call release(r) to release the resources.
                */
                static eldata get_data( Readline * r )
                {
                        iterator it = map().find( r );
                        if( it != map().end() ) return (*it).second;
                        eldata eld;
                        EditLine * el = ::el_init( "libreadline_cpp", stdin, stdout, stderr );
			//CERR << "Setting up EditLine: " << std::hex << el << '\n';
                        eld.el = el;
                        ::el_set(el, EL_EDITOR, "emacs");	/* Default editor is emacs		*/
                        ::el_set(el, EL_SIGNAL, 1);	/* Handle signals gracefully	*/
                        ::el_set( el, EL_BIND, "^R", "em-inc-search-prev", NULL );
                        ::el_set( el, EL_BIND, "^S", "em-inc-search-next", NULL );
                        ::el_set( el, EL_BIND, "^W", "ed-delete-prev-word", NULL ); // this varies from machine to machine, but i prefer this to the el default
                        ::el_set(el, EL_PROMPT, readline_prompt);	/* Set the prompt function	*/
                        // todo: bind in el's history support. Currently using home-grown mish-mash.

                        History * hist = history_init();
                        eld.hist = hist;
                        ::history( hist, &eld.hevt, H_SETSIZE, MAX_HISTORY_SIZE );
                        el_set(el, EL_HIST, ::history, hist );

                        map()[r] = eld;
                        return eld;
                }

                /**
                   r should call this function, passing itself, to get
                   it's EditLine "member."

		   Bug: we currently use the shared 
                */
                static EditLine * get_el( Readline * r )
                {
#if LIBREADLINECPP_USE_LIBEDITLINE
                        EditLine * el = ::el_readline_el();
                        static bool inited = false;
                        if( (!inited) && (inited = true) )
                        {
				::el_set(el, EL_EDITOR, "emacs");	/* Default editor is emacs		*/
				::el_set(el, EL_SIGNAL, 1);	/* Handle signals gracefully	*/
				::el_set( el, EL_BIND, "^R", "em-inc-search-prev", NULL );
				::el_set( el, EL_BIND, "^S", "em-inc-search-next", NULL );
				::el_set( el, EL_BIND, "^W", "ed-delete-prev-word", NULL ); // this varies from machine to machine, but i prefer this to the el default
				//  now HTF to map the delete key to ^H?
                        }
                        return el;
#else
			// libedit doesn't offer a way to modify the readline-compat-mode object
			return 0;
#endif //LIBREADLINECPP_USE_GENUINE_LIBEDIT
                }

                /**
                   r should call this function from it's dtor, passing
                   itself, to free it's EditLine "member."
                */
                static bool release( Readline * r )
                {
			iterator it = map().find( r );
			if( it == map().end() ) return false;
			eldata d = (*it).second;
			map().erase( it );
			el_end(d.el);
			history_end(d.hist);
                        return true;
                }
        private:
                typedef std::map<Readline *,eldata> map_type;
                typedef map_type::iterator iterator;
                typedef map_type::const_iterator const_iterator;
                /**
                   Internal-use map.
                */
                static map_type & map()
                {
                        static map_type bob;
                        return bob;
                }
        }; // struct el_holder

#endif // (LIBREADLINECPP_USE_LIBEDITLINE)



        void Readline_cleanup_terminal()
        {
#if LIBREADLINECPP_USE_LIBREADLINE
                rl_cleanup_after_signal();
#endif
        }

        Readline::Readline()
        {
                static bool donethat = false;
                if( ! donethat && (donethat=true) )
                {
                        ::atexit( Readline_cleanup_terminal );
#if LIBREADLINECPP_USE_LIBEDITLINE
			el_holder::get_el(this);
#endif
                }
                return;
        }
        Readline::Readline( const std::string &historyFileName )
        {
                this->load_history( historyFileName );
        }
        Readline::~Readline()
        {
                if( !this->m_filename.empty() ) 
                {
                        this->save_history( m_filename );
                }
#if LIBREADLINECPP_USE_LIBEDITLINE
                el_holder::release(this);
#endif
        }



        const std::string &
        Readline::theline()
        {
                return this->m_preline;
        }

        const std::string &
        Readline::readline( const std::string & prompt )
        {
                bool b;
                return this->readline( prompt, b );
        }




        const std::string &
        Readline::readline( const std::string & prompt, bool & breakOut )
        {
                // This func is a mess. It's time to refactor the various
                // readline functionalities into subclasses, or at least
                // separate functions.

                ////////////////////////////////////////////////////
                // first-time init...
                static bool inited = false;
                if( !inited && (inited=true) )
                {
#if LIBREADLINECPP_USE_LIBREADLINE
                        rl_catch_signals = 1;
                        rl_catch_sigwinch = 1;
                        rl_set_signals(); // need to be called every time?
#endif

#if USE_EDIT
                        using_history();
                        stifle_history( MAX_HISTORY_SIZE );
#else
                        std::cerr << __FILE__ << ":"<<__LINE__<<": Warning: class readlinecpp::Readline was compiled without support for an interactive input. No interactive editing will be possible." << std::endl;
#endif // USE_EDIT
                } // !inited
                // end first-time init
                ////////////////////////////////////////////////////

                std::string & theline = this->m_preline;

#if LIBREADLINECPP_USE_LIBEDITLINE
//                 start_over: // ACK! My first GOTO since BASIC!
                // ^^^ this is where we come back to if we read in
                // and dispatch a libeditline built-in command.
#endif // editline?

                breakOut = false;
                theline = "";


#if READLINE_USE_SIGNALS ////////////////////////////// set up Ctrl-C handler
                typedef void (*signalfunc)(int);
                signalfunc old_sighandler = signal( SIGINT, ::Readline_SIGINT );
                if( 0 == sigsetjmp( Readline_ctrl_c_jmp_buffer, 1 /* if 0 i get weird results :\ */ ) )
                { // enter pre-signal input mode (default mode)...
#endif // #if READLINE_USE_SIGNALS


#if USE_EDIT ////////////////////////////////////////////////////////////////////////
                        char * line_read = 0;
                        line_read = ::readline( const_cast<char *>(prompt.c_str()) );
                        if( line_read && *line_read )
                        {
                                theline = line_read;
                        }
                        else if( (char *)NULL == line_read )
                        { // libreadline docs say this == EOF
                                // CERR << "Looks like EOF?\n";
                                breakOut = true;
                                // editline apparently does not do this :(
                                // Aha - that's why editline's gets()
                                // left the trailing newline on the input!

                        }
                        if( line_read )
                        {
                                free(line_read);
                        }

#else ////////////////////// no edit/readline? fall back to cin...
                        std::istream & is = std::cin;
                        std::cout << prompt.c_str();
                        std::getline( is, theline );
                        if( is.eof() )
                        {
                                breakOut = true;
                                theline = std::string();
                                is.clear(); // evil, but avoids an endless loop.
                        }
#endif // use cin?
////////////////////////////////////////////////////////////////////////


#if READLINE_USE_SIGNALS /////////////////////////////// returning from a ctrl-c
                } else {
                        theline = std::string();
                        breakOut = false;
                }
                signal( SIGINT, old_sighandler ); // SIG_DFL );
                //std::cout << "readline(): ["<<theline<<"]"<<std::endl;
#endif // READLINE_USE_SIGNALS


                if( !breakOut && ! theline.empty() )
                {
                        this->add_history(theline);
                }
                return theline;
        }

        std::string Readline::rl_implementation_name()
        {
                return LIBREADLINE_CPP_IMPLEMENTATION_NAME;
        }


        void
        Readline::add_history( const std::string &line )
        {
                if( line.empty() ) return;
                Readline::history_list & h = this->m_hist;
                /* if item exists in our list, remove the old one (effectively moves it to the end of the list) */
//                 Readline::history_list::iterator it = std::find( h.begin(), h.end(), line );
//                 bool found = it != h.end();
//                 if( found )
//                 {
//                         h.erase( it );
//                 }
                h.push_back( line );
                size_t sz = h.size();
                if( sz > MAX_HISTORY_SIZE )
                {
                        Readline::history_list::iterator it = h.begin();
                        std::advance( it, sz % MAX_HISTORY_SIZE ); // reminder: linear time for std::list ... :(
                        h.erase( h.begin(), it );
                }
#if USE_EDIT
                ::add_history( line.c_str() );
                // i really only want to add line to ::add_history()
                // if we didn't already have it, else the discrepancy
                // between this class' history and libreadline's
                // becomes more apparent. :/ BUT... then libreadline
                // only has the older entry, and it's not at the end
                // of the list, as the user would expect :/.

                // i'm having trouble compiling with libhistory's
                // HISTORY_STATE (maybe a namespace thing, like the
                // 'environment' class had with C's "environment"), but
                // i think that struct holds the key to solving this.
#endif // USE_EDIT?
        }

        Readline::history_list &
        Readline::history()
        {
                return this->m_hist;
        }
        const Readline::history_list &
        Readline::history() const
        {
                return this->m_hist;
        }

        bool
        Readline::save_history( std::ostream &os )
        {
                if( ! os ) return false;
                Readline::history_list & h = this->history();
                if( h.size() == 0 ) return true;
                std::copy( h.begin(), h.end(), std::ostream_iterator<std::string>(os,"\n") );
                return true;
        }

        bool
        Readline::save_history( const std::string & filename )
        {
                // we actually want to save even if we have 0 history,
                // to make it possible for the user to clear the
                // history.
                std::string fn = filename;
                if( fn.empty() ) fn = this->m_filename;
                else this->m_filename = fn;
                if( fn.empty() ) return false;
                std::ofstream os( fn.c_str() );
                return save_history( os );
        }

        void
        Readline::clear_history()
        {
                Readline::history_list & h = this->history();
                if( 0 == h.size() ) return;
                h.erase( h.begin(), h.end() );
#if USE_EDIT
                ::clear_history();
#endif
        }

        bool
        Readline::load_history( std::istream &is )
        {
                if( ! is ) return false;
                this->clear_history();
                std::string buff;
                while( ! std::getline( is, buff ).eof() )
                {
                        this->add_history( buff );
                }
                return true;
        }


        bool
        Readline::load_history( const std::string & filename )
        {
                std::string fn = filename;
                if( fn.empty() ) fn = this->m_filename;
                else this->m_filename = fn;
                if( fn.empty() ) return false;
                std::ifstream is( fn.c_str() );
                return load_history( is );
        }


} // namespace readlinecpp

#undef USE_EDIT

