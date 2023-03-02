/* A Bison parser, made by GNU Bison 3.8.2.  */

/* Bison implementation for Yacc-like parsers in C

   Copyright (C) 1984, 1989-1990, 2000-2015, 2018-2021 Free Software Foundation,
   Inc.

   This program is free software: you can redistribute it and/or modify
   it under the terms of the GNU General Public License as published by
   the Free Software Foundation, either version 3 of the License, or
   (at your option) any later version.

   This program is distributed in the hope that it will be useful,
   but WITHOUT ANY WARRANTY; without even the implied warranty of
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
   GNU General Public License for more details.

   You should have received a copy of the GNU General Public License
   along with this program.  If not, see <https://www.gnu.org/licenses/>.  */

/* As a special exception, you may create a larger work that contains
   part or all of the Bison parser skeleton and distribute that work
   under terms of your choice, so long as that work isn't itself a
   parser generator using the skeleton or a modified version thereof
   as a parser skeleton.  Alternatively, if you modify or redistribute
   the parser skeleton itself, you may (at your option) remove this
   special exception, which will cause the skeleton and the resulting
   Bison output files to be licensed under the GNU General Public
   License without this special exception.

   This special exception was added by the Free Software Foundation in
   version 2.2 of Bison.  */

/* C LALR(1) parser skeleton written by Richard Stallman, by
   simplifying the original so-called "semantic" parser.  */

/* DO NOT RELY ON FEATURES THAT ARE NOT DOCUMENTED in the manual,
   especially those whose name start with YY_ or yy_.  They are
   private implementation details that can be changed or removed.  */

/* All symbols defined below should begin with yy or YY, to avoid
   infringing on user name space.  This should be done even for local
   variables, as they might otherwise be expanded by user macros.
   There are some unavoidable exceptions within include files to
   define necessary library symbols; they are noted "INFRINGES ON
   USER NAME SPACE" below.  */

/* Identify Bison output, and Bison version.  */
#define YYBISON 30802

/* Bison version string.  */
#define YYBISON_VERSION "3.8.2"

/* Skeleton name.  */
#define YYSKELETON_NAME "yacc.c"

/* Pure parsers.  */
#define YYPURE 0

/* Push parsers.  */
#define YYPUSH 0

/* Pull parsers.  */
#define YYPULL 1





# ifndef YY_CAST
#  ifdef __cplusplus
#   define YY_CAST(Type, Val) static_cast<Type> (Val)
#   define YY_REINTERPRET_CAST(Type, Val) reinterpret_cast<Type> (Val)
#  else
#   define YY_CAST(Type, Val) ((Type) (Val))
#   define YY_REINTERPRET_CAST(Type, Val) ((Type) (Val))
#  endif
# endif
# ifndef YY_NULLPTR
#  if defined __cplusplus
#   if 201103L <= __cplusplus
#    define YY_NULLPTR nullptr
#   else
#    define YY_NULLPTR 0
#   endif
#  else
#   define YY_NULLPTR ((void*)0)
#  endif
# endif


/* Debug traces.  */
#ifndef YYDEBUG
# define YYDEBUG 0
#endif
#if YYDEBUG
extern int yydebug;
#endif

/* Token kinds.  */
#ifndef YYTOKENTYPE
# define YYTOKENTYPE
  enum yytokentype
  {
    YYEMPTY = -2,
    YYEOF = 0,                     /* "end of file"  */
    YYerror = 256,                 /* error  */
    YYUNDEF = 257,                 /* "invalid token"  */
    let = 258,                     /* let  */
    static = 259,                  /* static  */
    here = 260,                    /* here  */
    mut = 261,                     /* mut  */
    goto = 262,                    /* goto  */
    type = 263,                    /* type  */
    lambda = 264,                  /* lambda  */
    to = 265,                      /* to  */
    if = 266,                      /* if  */
    int = 267,                     /* int  */
    float = 268,                   /* float  */
    char = 269,                    /* char  */
    str = 270,                     /* str  */
    var = 271,                     /* var  */
    lopMAX_LEVEL = 272,            /* lopMAX_LEVEL  */
    lopASSIGN_LEVEL = 273,         /* lopASSIGN_LEVEL  */
    lopIN_LEVEL = 274,             /* lopIN_LEVEL  */
    ropMAX_LEVEL = 275,            /* ropMAX_LEVEL  */
    ropIN_LEVEL = 276,             /* ropIN_LEVEL  */
    ropASSIGN_LEVEL = 277,         /* ropASSIGN_LEVEL  */
    string = 278,                  /* string  */
    matches = 279,                 /* matches  */
    for = 280,                     /* for  */
    while = 281,                   /* while  */
    in = 282,                      /* in  */
    else = 283,                    /* else  */
    cons = 284                     /* cons  */
  };
  typedef enum yytokentype yytoken_kind_t;
#endif

/* Value type.  */
#if ! defined YYSTYPE && ! defined YYSTYPE_IS_DECLARED
typedef int YYSTYPE;
# define YYSTYPE_IS_TRIVIAL 1
# define YYSTYPE_IS_DECLARED 1
#endif


extern YYSTYPE yylval;


int yyparse (void);



/* Symbol kind.  */
enum yysymbol_kind_t
{
  YYSYMBOL_YYEMPTY = -2,
  YYSYMBOL_YYEOF = 0,                      /* "end of file"  */
  YYSYMBOL_YYerror = 1,                    /* error  */
  YYSYMBOL_YYUNDEF = 2,                    /* "invalid token"  */
  YYSYMBOL_3_ = 3,                         /* ';'  */
  YYSYMBOL_let = 4,                        /* let  */
  YYSYMBOL_static = 5,                     /* static  */
  YYSYMBOL_here = 6,                       /* here  */
  YYSYMBOL_mut = 7,                        /* mut  */
  YYSYMBOL_goto = 8,                       /* goto  */
  YYSYMBOL_type = 9,                       /* type  */
  YYSYMBOL_lambda = 10,                    /* lambda  */
  YYSYMBOL_to = 11,                        /* to  */
  YYSYMBOL_if = 12,                        /* if  */
  YYSYMBOL_13_ = 13,                       /* '['  */
  YYSYMBOL_14_ = 14,                       /* ']'  */
  YYSYMBOL_int = 15,                       /* int  */
  YYSYMBOL_float = 16,                     /* float  */
  YYSYMBOL_char = 17,                      /* char  */
  YYSYMBOL_str = 18,                       /* str  */
  YYSYMBOL_var = 19,                       /* var  */
  YYSYMBOL_lopMAX_LEVEL = 20,              /* lopMAX_LEVEL  */
  YYSYMBOL_lopASSIGN_LEVEL = 21,           /* lopASSIGN_LEVEL  */
  YYSYMBOL_lopIN_LEVEL = 22,               /* lopIN_LEVEL  */
  YYSYMBOL_ropMAX_LEVEL = 23,              /* ropMAX_LEVEL  */
  YYSYMBOL_ropIN_LEVEL = 24,               /* ropIN_LEVEL  */
  YYSYMBOL_ropASSIGN_LEVEL = 25,           /* ropASSIGN_LEVEL  */
  YYSYMBOL_26_ = 26,                       /* '='  */
  YYSYMBOL_27_ = 27,                       /* ','  */
  YYSYMBOL_28_ = 28,                       /* '{'  */
  YYSYMBOL_29_ = 29,                       /* '}'  */
  YYSYMBOL_string = 30,                    /* string  */
  YYSYMBOL_31_ = 31,                       /* '('  */
  YYSYMBOL_32_ = 32,                       /* ')'  */
  YYSYMBOL_matches = 33,                   /* matches  */
  YYSYMBOL_for = 34,                       /* for  */
  YYSYMBOL_while = 35,                     /* while  */
  YYSYMBOL_in = 36,                        /* in  */
  YYSYMBOL_else = 37,                      /* else  */
  YYSYMBOL_cons = 38,                      /* cons  */
  YYSYMBOL_39_ = 39,                       /* '|'  */
  YYSYMBOL_YYACCEPT = 40,                  /* $accept  */
  YYSYMBOL_Stmt = 41,                      /* Stmt  */
  YYSYMBOL_Let = 42,                       /* Let  */
  YYSYMBOL_LetList = 43,                   /* LetList  */
  YYSYMBOL_VAR = 44,                       /* VAR  */
  YYSYMBOL_LexprMAX_LEVEL = 45,            /* LexprMAX_LEVEL  */
  YYSYMBOL_RexprMAX_LEVEL = 46,            /* RexprMAX_LEVEL  */
  YYSYMBOL_LexprASSIGN_LEVEL = 47,         /* LexprASSIGN_LEVEL  */
  YYSYMBOL_RexprASSIGN_LEVEL = 48,         /* RexprASSIGN_LEVEL  */
  YYSYMBOL_LexprIN_LEVEL = 49,             /* LexprIN_LEVEL  */
  YYSYMBOL_LexprIN_LEVELNoBrace = 50,      /* LexprIN_LEVELNoBrace  */
  YYSYMBOL_RexprIN_LEVEL = 51,             /* RexprIN_LEVEL  */
  YYSYMBOL_RexprIN_LEVELNoBrace = 52,      /* RexprIN_LEVELNoBrace  */
  YYSYMBOL_LexprIF_LEVEL = 53,             /* LexprIF_LEVEL  */
  YYSYMBOL_LexprIF_LEVELNoBrace = 54,      /* LexprIF_LEVELNoBrace  */
  YYSYMBOL_LexprAPPLICATION_LEVEL = 55,    /* LexprAPPLICATION_LEVEL  */
  YYSYMBOL_LexprAPPLICATION_LEVELNoBrace = 56, /* LexprAPPLICATION_LEVELNoBrace  */
  YYSYMBOL_LitNoBrace = 57,                /* LitNoBrace  */
  YYSYMBOL_Lit = 58,                       /* Lit  */
  YYSYMBOL_InnerList = 59,                 /* InnerList  */
  YYSYMBOL_InnerMatch = 60,                /* InnerMatch  */
  YYSYMBOL_InnerStruct = 61,               /* InnerStruct  */
  YYSYMBOL_ReturningIf = 62,               /* ReturningIf  */
  YYSYMBOL_NonReturningIf = 63,            /* NonReturningIf  */
  YYSYMBOL_For = 64,                       /* For  */
  YYSYMBOL_OldFor = 65,                    /* OldFor  */
  YYSYMBOL_InFor = 66,                     /* InFor  */
  YYSYMBOL_ReturningBlock = 67,            /* ReturningBlock  */
  YYSYMBOL_NonReturningBlock = 68,         /* NonReturningBlock  */
  YYSYMBOL_InnerBlock = 69,                /* InnerBlock  */
  YYSYMBOL_While = 70                      /* While  */
};
typedef enum yysymbol_kind_t yysymbol_kind_t;




#ifdef short
# undef short
#endif

/* On compilers that do not define __PTRDIFF_MAX__ etc., make sure
   <limits.h> and (if available) <stdint.h> are included
   so that the code can choose integer types of a good width.  */

#ifndef __PTRDIFF_MAX__
# include <limits.h> /* INFRINGES ON USER NAME SPACE */
# if defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stdint.h> /* INFRINGES ON USER NAME SPACE */
#  define YY_STDINT_H
# endif
#endif

/* Narrow types that promote to a signed type and that can represent a
   signed or unsigned integer of at least N bits.  In tables they can
   save space and decrease cache pressure.  Promoting to a signed type
   helps avoid bugs in integer arithmetic.  */

#ifdef __INT_LEAST8_MAX__
typedef __INT_LEAST8_TYPE__ yytype_int8;
#elif defined YY_STDINT_H
typedef int_least8_t yytype_int8;
#else
typedef signed char yytype_int8;
#endif

#ifdef __INT_LEAST16_MAX__
typedef __INT_LEAST16_TYPE__ yytype_int16;
#elif defined YY_STDINT_H
typedef int_least16_t yytype_int16;
#else
typedef short yytype_int16;
#endif

/* Work around bug in HP-UX 11.23, which defines these macros
   incorrectly for preprocessor constants.  This workaround can likely
   be removed in 2023, as HPE has promised support for HP-UX 11.23
   (aka HP-UX 11i v2) only through the end of 2022; see Table 2 of
   <https://h20195.www2.hpe.com/V2/getpdf.aspx/4AA4-7673ENW.pdf>.  */
#ifdef __hpux
# undef UINT_LEAST8_MAX
# undef UINT_LEAST16_MAX
# define UINT_LEAST8_MAX 255
# define UINT_LEAST16_MAX 65535
#endif

#if defined __UINT_LEAST8_MAX__ && __UINT_LEAST8_MAX__ <= __INT_MAX__
typedef __UINT_LEAST8_TYPE__ yytype_uint8;
#elif (!defined __UINT_LEAST8_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST8_MAX <= INT_MAX)
typedef uint_least8_t yytype_uint8;
#elif !defined __UINT_LEAST8_MAX__ && UCHAR_MAX <= INT_MAX
typedef unsigned char yytype_uint8;
#else
typedef short yytype_uint8;
#endif

#if defined __UINT_LEAST16_MAX__ && __UINT_LEAST16_MAX__ <= __INT_MAX__
typedef __UINT_LEAST16_TYPE__ yytype_uint16;
#elif (!defined __UINT_LEAST16_MAX__ && defined YY_STDINT_H \
       && UINT_LEAST16_MAX <= INT_MAX)
typedef uint_least16_t yytype_uint16;
#elif !defined __UINT_LEAST16_MAX__ && USHRT_MAX <= INT_MAX
typedef unsigned short yytype_uint16;
#else
typedef int yytype_uint16;
#endif

#ifndef YYPTRDIFF_T
# if defined __PTRDIFF_TYPE__ && defined __PTRDIFF_MAX__
#  define YYPTRDIFF_T __PTRDIFF_TYPE__
#  define YYPTRDIFF_MAXIMUM __PTRDIFF_MAX__
# elif defined PTRDIFF_MAX
#  ifndef ptrdiff_t
#   include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  endif
#  define YYPTRDIFF_T ptrdiff_t
#  define YYPTRDIFF_MAXIMUM PTRDIFF_MAX
# else
#  define YYPTRDIFF_T long
#  define YYPTRDIFF_MAXIMUM LONG_MAX
# endif
#endif

#ifndef YYSIZE_T
# ifdef __SIZE_TYPE__
#  define YYSIZE_T __SIZE_TYPE__
# elif defined size_t
#  define YYSIZE_T size_t
# elif defined __STDC_VERSION__ && 199901 <= __STDC_VERSION__
#  include <stddef.h> /* INFRINGES ON USER NAME SPACE */
#  define YYSIZE_T size_t
# else
#  define YYSIZE_T unsigned
# endif
#endif

#define YYSIZE_MAXIMUM                                  \
  YY_CAST (YYPTRDIFF_T,                                 \
           (YYPTRDIFF_MAXIMUM < YY_CAST (YYSIZE_T, -1)  \
            ? YYPTRDIFF_MAXIMUM                         \
            : YY_CAST (YYSIZE_T, -1)))

#define YYSIZEOF(X) YY_CAST (YYPTRDIFF_T, sizeof (X))


/* Stored state numbers (used for stacks). */
typedef yytype_uint8 yy_state_t;

/* State numbers in computations.  */
typedef int yy_state_fast_t;

#ifndef YY_
# if defined YYENABLE_NLS && YYENABLE_NLS
#  if ENABLE_NLS
#   include <libintl.h> /* INFRINGES ON USER NAME SPACE */
#   define YY_(Msgid) dgettext ("bison-runtime", Msgid)
#  endif
# endif
# ifndef YY_
#  define YY_(Msgid) Msgid
# endif
#endif


#ifndef YY_ATTRIBUTE_PURE
# if defined __GNUC__ && 2 < __GNUC__ + (96 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_PURE __attribute__ ((__pure__))
# else
#  define YY_ATTRIBUTE_PURE
# endif
#endif

#ifndef YY_ATTRIBUTE_UNUSED
# if defined __GNUC__ && 2 < __GNUC__ + (7 <= __GNUC_MINOR__)
#  define YY_ATTRIBUTE_UNUSED __attribute__ ((__unused__))
# else
#  define YY_ATTRIBUTE_UNUSED
# endif
#endif

/* Suppress unused-variable warnings by "using" E.  */
#if ! defined lint || defined __GNUC__
# define YY_USE(E) ((void) (E))
#else
# define YY_USE(E) /* empty */
#endif

/* Suppress an incorrect diagnostic about yylval being uninitialized.  */
#if defined __GNUC__ && ! defined __ICC && 406 <= __GNUC__ * 100 + __GNUC_MINOR__
# if __GNUC__ * 100 + __GNUC_MINOR__ < 407
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")
# else
#  define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN                           \
    _Pragma ("GCC diagnostic push")                                     \
    _Pragma ("GCC diagnostic ignored \"-Wuninitialized\"")              \
    _Pragma ("GCC diagnostic ignored \"-Wmaybe-uninitialized\"")
# endif
# define YY_IGNORE_MAYBE_UNINITIALIZED_END      \
    _Pragma ("GCC diagnostic pop")
#else
# define YY_INITIAL_VALUE(Value) Value
#endif
#ifndef YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
# define YY_IGNORE_MAYBE_UNINITIALIZED_END
#endif
#ifndef YY_INITIAL_VALUE
# define YY_INITIAL_VALUE(Value) /* Nothing. */
#endif

#if defined __cplusplus && defined __GNUC__ && ! defined __ICC && 6 <= __GNUC__
# define YY_IGNORE_USELESS_CAST_BEGIN                          \
    _Pragma ("GCC diagnostic push")                            \
    _Pragma ("GCC diagnostic ignored \"-Wuseless-cast\"")
# define YY_IGNORE_USELESS_CAST_END            \
    _Pragma ("GCC diagnostic pop")
#endif
#ifndef YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_BEGIN
# define YY_IGNORE_USELESS_CAST_END
#endif


#define YY_ASSERT(E) ((void) (0 && (E)))

#if !defined yyoverflow

/* The parser invokes alloca or malloc; define the necessary symbols.  */

# ifdef YYSTACK_USE_ALLOCA
#  if YYSTACK_USE_ALLOCA
#   ifdef __GNUC__
#    define YYSTACK_ALLOC __builtin_alloca
#   elif defined __BUILTIN_VA_ARG_INCR
#    include <alloca.h> /* INFRINGES ON USER NAME SPACE */
#   elif defined _AIX
#    define YYSTACK_ALLOC __alloca
#   elif defined _MSC_VER
#    include <malloc.h> /* INFRINGES ON USER NAME SPACE */
#    define alloca _alloca
#   else
#    define YYSTACK_ALLOC alloca
#    if ! defined _ALLOCA_H && ! defined EXIT_SUCCESS
#     include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
      /* Use EXIT_SUCCESS as a witness for stdlib.h.  */
#     ifndef EXIT_SUCCESS
#      define EXIT_SUCCESS 0
#     endif
#    endif
#   endif
#  endif
# endif

# ifdef YYSTACK_ALLOC
   /* Pacify GCC's 'empty if-body' warning.  */
#  define YYSTACK_FREE(Ptr) do { /* empty */; } while (0)
#  ifndef YYSTACK_ALLOC_MAXIMUM
    /* The OS might guarantee only one guard page at the bottom of the stack,
       and a page size can be as small as 4096 bytes.  So we cannot safely
       invoke alloca (N) if N exceeds 4096.  Use a slightly smaller number
       to allow for a few compiler-allocated temporary stack slots.  */
#   define YYSTACK_ALLOC_MAXIMUM 4032 /* reasonable circa 2006 */
#  endif
# else
#  define YYSTACK_ALLOC YYMALLOC
#  define YYSTACK_FREE YYFREE
#  ifndef YYSTACK_ALLOC_MAXIMUM
#   define YYSTACK_ALLOC_MAXIMUM YYSIZE_MAXIMUM
#  endif
#  if (defined __cplusplus && ! defined EXIT_SUCCESS \
       && ! ((defined YYMALLOC || defined malloc) \
             && (defined YYFREE || defined free)))
#   include <stdlib.h> /* INFRINGES ON USER NAME SPACE */
#   ifndef EXIT_SUCCESS
#    define EXIT_SUCCESS 0
#   endif
#  endif
#  ifndef YYMALLOC
#   define YYMALLOC malloc
#   if ! defined malloc && ! defined EXIT_SUCCESS
void *malloc (YYSIZE_T); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
#  ifndef YYFREE
#   define YYFREE free
#   if ! defined free && ! defined EXIT_SUCCESS
void free (void *); /* INFRINGES ON USER NAME SPACE */
#   endif
#  endif
# endif
#endif /* !defined yyoverflow */

#if (! defined yyoverflow \
     && (! defined __cplusplus \
         || (defined YYSTYPE_IS_TRIVIAL && YYSTYPE_IS_TRIVIAL)))

/* A type that is properly aligned for any stack member.  */
union yyalloc
{
  yy_state_t yyss_alloc;
  YYSTYPE yyvs_alloc;
};

/* The size of the maximum gap between one aligned stack and the next.  */
# define YYSTACK_GAP_MAXIMUM (YYSIZEOF (union yyalloc) - 1)

/* The size of an array large to enough to hold all stacks, each with
   N elements.  */
# define YYSTACK_BYTES(N) \
     ((N) * (YYSIZEOF (yy_state_t) + YYSIZEOF (YYSTYPE)) \
      + YYSTACK_GAP_MAXIMUM)

# define YYCOPY_NEEDED 1

/* Relocate STACK from its old location to the new one.  The
   local variables YYSIZE and YYSTACKSIZE give the old and new number of
   elements in the stack, and YYPTR gives the new location of the
   stack.  Advance YYPTR to a properly aligned location for the next
   stack.  */
# define YYSTACK_RELOCATE(Stack_alloc, Stack)                           \
    do                                                                  \
      {                                                                 \
        YYPTRDIFF_T yynewbytes;                                         \
        YYCOPY (&yyptr->Stack_alloc, Stack, yysize);                    \
        Stack = &yyptr->Stack_alloc;                                    \
        yynewbytes = yystacksize * YYSIZEOF (*Stack) + YYSTACK_GAP_MAXIMUM; \
        yyptr += yynewbytes / YYSIZEOF (*yyptr);                        \
      }                                                                 \
    while (0)

#endif

#if defined YYCOPY_NEEDED && YYCOPY_NEEDED
/* Copy COUNT objects from SRC to DST.  The source and destination do
   not overlap.  */
# ifndef YYCOPY
#  if defined __GNUC__ && 1 < __GNUC__
#   define YYCOPY(Dst, Src, Count) \
      __builtin_memcpy (Dst, Src, YY_CAST (YYSIZE_T, (Count)) * sizeof (*(Src)))
#  else
#   define YYCOPY(Dst, Src, Count)              \
      do                                        \
        {                                       \
          YYPTRDIFF_T yyi;                      \
          for (yyi = 0; yyi < (Count); yyi++)   \
            (Dst)[yyi] = (Src)[yyi];            \
        }                                       \
      while (0)
#  endif
# endif
#endif /* !YYCOPY_NEEDED */

/* YYFINAL -- State number of the termination state.  */
#define YYFINAL  76
/* YYLAST -- Last index in YYTABLE.  */
#define YYLAST   823

/* YYNTOKENS -- Number of terminals.  */
#define YYNTOKENS  40
/* YYNNTS -- Number of nonterminals.  */
#define YYNNTS  31
/* YYNRULES -- Number of rules.  */
#define YYNRULES  93
/* YYNSTATES -- Number of states.  */
#define YYNSTATES  194

/* YYMAXUTOK -- Last valid token kind.  */
#define YYMAXUTOK   284


/* YYTRANSLATE(TOKEN-NUM) -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex, with out-of-bounds checking.  */
#define YYTRANSLATE(YYX)                                \
  (0 <= (YYX) && (YYX) <= YYMAXUTOK                     \
   ? YY_CAST (yysymbol_kind_t, yytranslate[YYX])        \
   : YYSYMBOL_YYUNDEF)

/* YYTRANSLATE[TOKEN-NUM] -- Symbol number corresponding to TOKEN-NUM
   as returned by yylex.  */
static const yytype_int8 yytranslate[] =
{
       0,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
      31,    32,     2,     2,    27,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     3,
       2,    26,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,    13,     2,    14,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,    28,    39,    29,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     2,     2,     2,     2,
       2,     2,     2,     2,     2,     2,     1,     2,     4,     5,
       6,     7,     8,     9,    10,    11,    12,    15,    16,    17,
      18,    19,    20,    21,    22,    23,    24,    25,    30,    33,
      34,    35,    36,    37,    38
};

#if YYDEBUG
/* YYRLINE[YYN] -- Source line where rule number YYN was defined.  */
static const yytype_uint8 yyrline[] =
{
       0,     8,     8,     9,    10,    11,    12,    13,    14,    16,
      18,    18,    20,    21,    22,    23,    34,    35,    37,    38,
      40,    41,    43,    44,    45,    47,    48,    50,    51,    52,
      53,    54,    55,    60,    61,    62,    63,    66,    67,    68,
      71,    71,    73,    73,    75,    76,    77,    78,    79,    80,
      81,    82,    83,    84,    85,    86,    87,    88,    89,    90,
      91,    92,    94,    94,    94,    96,    97,    99,   100,   102,
     103,   104,   105,   107,   108,   110,   111,   112,   114,   115,
     117,   118,   119,   120,   121,   122,   123,   125,   127,   129,
     129,   131,   132,   134
};
#endif

/** Accessing symbol of state STATE.  */
#define YY_ACCESSING_SYMBOL(State) YY_CAST (yysymbol_kind_t, yystos[State])

#if YYDEBUG || 0
/* The user-facing name of the symbol whose (internal) number is
   YYSYMBOL.  No bounds checking.  */
static const char *yysymbol_name (yysymbol_kind_t yysymbol) YY_ATTRIBUTE_UNUSED;

/* YYTNAME[SYMBOL-NUM] -- String name of the symbol SYMBOL-NUM.
   First, the terminals, then, starting at YYNTOKENS, nonterminals.  */
static const char *const yytname[] =
{
  "\"end of file\"", "error", "\"invalid token\"", "';'", "let", "static",
  "here", "mut", "goto", "type", "lambda", "to", "if", "'['", "']'", "int",
  "float", "char", "str", "var", "lopMAX_LEVEL", "lopASSIGN_LEVEL",
  "lopIN_LEVEL", "ropMAX_LEVEL", "ropIN_LEVEL", "ropASSIGN_LEVEL", "'='",
  "','", "'{'", "'}'", "string", "'('", "')'", "matches", "for", "while",
  "in", "else", "cons", "'|'", "$accept", "Stmt", "Let", "LetList", "VAR",
  "LexprMAX_LEVEL", "RexprMAX_LEVEL", "LexprASSIGN_LEVEL",
  "RexprASSIGN_LEVEL", "LexprIN_LEVEL", "LexprIN_LEVELNoBrace",
  "RexprIN_LEVEL", "RexprIN_LEVELNoBrace", "LexprIF_LEVEL",
  "LexprIF_LEVELNoBrace", "LexprAPPLICATION_LEVEL",
  "LexprAPPLICATION_LEVELNoBrace", "LitNoBrace", "Lit", "InnerList",
  "InnerMatch", "InnerStruct", "ReturningIf", "NonReturningIf", "For",
  "OldFor", "InFor", "ReturningBlock", "NonReturningBlock", "InnerBlock",
  "While", YY_NULLPTR
};

static const char *
yysymbol_name (yysymbol_kind_t yysymbol)
{
  return yytname[yysymbol];
}
#endif

#define YYPACT_NINF (-72)

#define yypact_value_is_default(Yyn) \
  ((Yyn) == YYPACT_NINF)

#define YYTABLE_NINF (-1)

#define yytable_value_is_error(Yyn) \
  0

/* YYPACT[STATE-NUM] -- Index in YYTABLE of the portion describing
   STATE-NUM.  */
static const yytype_int16 yypact[] =
{
     307,   571,    54,   -12,    12,    52,   757,    99,   571,   -72,
     -72,   -72,   -72,   237,   -72,   339,   598,    99,   -17,    67,
     -72,   -72,    27,   -72,   151,   -72,    61,   655,   -72,   -72,
     -72,   -72,   -72,   -72,   -72,   -72,    99,   307,    13,   -72,
      84,   -72,    29,   -72,    83,   757,   683,   735,    85,   102,
     785,   -72,   103,   -72,    78,    38,   -72,   -72,   626,   107,
     272,   368,    75,   397,   106,   114,   -72,   128,   204,    42,
     178,    34,   121,   121,   121,   116,   -72,   -72,   571,   571,
     571,   571,   571,   571,   -72,   123,   307,   -72,   571,   -72,
     -72,   -72,   703,   571,   792,   237,   117,   125,    99,    99,
     -72,   571,   571,   -72,   571,   571,   757,   -72,   -72,   -72,
      22,   -72,   133,   -72,   -72,   134,   -72,   -72,   426,   455,
     -72,   571,   140,    32,    99,   237,   -72,   -72,   -72,   143,
     115,   -72,   -72,   -72,   -72,   -72,   -72,   307,   -72,   -72,
      99,     9,    48,   -72,   -72,   -72,   -72,   103,   -72,   730,
     -72,   -72,   -72,   -72,   -72,    93,   571,    33,   208,   157,
     -72,   272,   571,   161,   -72,   -72,   -72,    99,   -72,   571,
     -72,    62,   484,   513,    43,    99,   -72,   156,   121,   -72,
     -72,   -72,    79,   -72,    87,   542,   -72,   571,   -72,   -72,
     -72,    96,   -72,   -72
};

/* YYDEFACT[STATE-NUM] -- Default reduction number in state STATE-NUM.
   Performed when YYTABLE does not specify something else to do.  Zero
   means the default is an error.  */
static const yytype_int8 yydefact[] =
{
       0,     0,     0,     0,     0,     0,     0,     0,     0,    44,
      45,    46,    12,     0,    47,     0,     0,     0,     0,     0,
       5,    48,     0,    21,    24,    26,    30,    36,    62,    41,
      33,     8,     2,    74,    77,     3,     0,     0,     0,    11,
       0,    14,     0,    13,     0,     0,     0,     0,     0,    32,
      39,    43,    66,    17,    19,     0,    90,    92,    36,     0,
       0,     0,     0,     0,     0,     0,    58,    66,    24,     0,
       0,     0,     0,     0,     0,     0,     1,     4,     0,     0,
       0,     0,     0,     0,    40,     0,     0,     9,     0,    15,
       7,     6,     0,     0,     0,     0,     0,    76,     0,     0,
      42,     0,     0,    61,     0,     0,     0,    63,    89,    91,
       0,    51,     0,    49,    50,     0,    57,    56,     0,     0,
      59,     0,     0,    19,     0,     0,    78,    79,    93,    72,
       0,    20,    25,    23,    22,    29,    35,     0,    10,    34,
       0,     0,     0,    31,    38,    16,    18,    65,    68,     0,
      88,    55,    54,    53,    52,     0,     0,     0,     0,    87,
      28,     0,     0,     0,    64,    37,    73,     0,    75,     0,
      60,     0,     0,     0,     0,     0,    71,    70,     0,    67,
      86,    84,     0,    83,     0,     0,    27,     0,    85,    81,
      82,     0,    69,    80
};

/* YYPGOTO[NTERM-NUM].  */
static const yytype_int16 yypgoto[] =
{
     -72,     6,   -72,   -72,   -72,    -2,   -43,     2,    -1,     8,
     -72,   -37,   -35,   -71,    -9,     4,   137,    -3,    -8,     1,
     -72,   -72,    51,    47,   -72,   -72,   -72,   -28,   -45,   -32,
     -72
};

/* YYDEFGOTO[NTERM-NUM].  */
static const yytype_uint8 yydefgoto[] =
{
       0,    57,    20,    38,    21,    52,    53,    54,    23,    24,
     159,    25,    48,    26,    49,    27,    50,    28,    29,    69,
      59,   130,    30,    31,    32,    72,    73,    33,    34,    60,
      35
};

/* YYTABLE[YYPACT[STATE-NUM]] -- What to do in state STATE-NUM.  If
   positive, shift that token.  If negative, reduce the rule whose
   number is the opposite.  If YYTABLE_NINF, syntax error.  */
static const yytype_uint8 yytable[] =
{
      39,    85,    22,    97,    51,    86,    19,    42,    74,    55,
      46,    75,   136,    67,    51,    22,    87,    58,   112,    84,
      96,    36,   139,    68,    71,    77,   115,   126,   127,   128,
      77,    43,    90,    51,   148,   158,   172,   137,    84,    22,
      88,    58,   132,    78,    51,   135,   185,   100,    78,    92,
      84,   150,   103,    78,    78,   102,    79,    96,   145,   146,
     167,    40,   110,   143,    78,   104,   109,    76,    67,   104,
     124,    44,   123,    41,   120,   145,   125,   131,    68,   133,
     134,   121,   132,    78,    84,    82,    91,   138,   110,   160,
     144,   100,   109,   161,   180,    51,    51,    22,   179,    78,
      78,   102,   147,    89,     2,    86,     4,   113,    78,    47,
     149,   188,     8,    95,     9,    10,    11,    78,    12,   189,
     104,    51,   155,   101,   157,   170,    98,    22,   193,    14,
      15,   165,   178,    97,   106,   129,   107,    51,   116,    22,
     186,    84,   163,   156,   164,     2,   117,     4,   118,   125,
       6,   137,    36,     8,   141,     9,    10,    11,   171,    12,
     174,   176,   142,    22,    51,   151,   152,   109,    37,   162,
      14,    15,    51,    79,   182,   184,    80,    81,    18,   175,
     177,   122,   187,     2,    94,     4,   192,   191,     6,   168,
      36,     8,   166,     9,    10,    11,     0,    12,    61,    62,
      63,    64,    65,     0,     0,     0,    37,     0,    14,    15,
      66,   173,     0,     2,     0,     4,    18,     0,     6,     0,
      36,     8,     0,     9,    10,    11,   119,    12,     0,    80,
      81,     0,     0,     0,     0,     0,    37,     0,    14,    15,
       0,     1,     2,     3,     4,     5,    18,     6,     0,     7,
       8,     0,     9,    10,    11,     0,    12,     0,     0,     0,
       0,     0,     0,     0,     0,    13,    56,    14,    15,     0,
       0,    16,    17,     0,     0,    18,     1,     2,     3,     4,
       5,     0,     6,     0,     7,     8,     0,     9,    10,    11,
       0,    12,     0,     0,     0,     0,     0,     0,     0,     0,
      13,   108,    14,    15,     0,     0,    16,    17,     0,     0,
      18,     1,     2,     3,     4,     5,     0,     6,     0,     7,
       8,     0,     9,    10,    11,     0,    12,     0,     0,     0,
       0,     0,     0,     0,     0,    13,     0,    14,    15,     0,
       0,    16,    17,     0,     2,    18,     4,     0,     0,     6,
       0,    36,     8,     0,     9,    10,    11,     0,    12,    61,
      62,    63,    64,    65,     0,     0,     0,    37,     0,    14,
      15,    66,     0,     2,     0,     4,     0,    18,     6,     0,
      36,     8,     0,     9,    10,    11,     0,    12,     0,     0,
       0,     0,     0,     0,     0,     0,    37,     0,    14,    15,
     111,     0,     2,     0,     4,     0,    18,     6,     0,    36,
       8,     0,     9,    10,    11,     0,    12,     0,     0,     0,
       0,     0,     0,     0,     0,    37,     0,    14,    15,   114,
       0,     2,     0,     4,     0,    18,     6,     0,    36,     8,
       0,     9,    10,    11,     0,    12,     0,     0,     0,     0,
       0,     0,     0,     0,    37,     0,    14,    15,   153,     0,
       2,     0,     4,     0,    18,     6,     0,    36,     8,     0,
       9,    10,    11,     0,    12,     0,     0,     0,     0,     0,
       0,     0,     0,    37,     0,    14,    15,   154,     0,     2,
       0,     4,     0,    18,     6,     0,    36,     8,     0,     9,
      10,    11,     0,    12,     0,     0,     0,     0,     0,     0,
       0,     0,    37,     0,    14,    15,   181,     0,     2,     0,
       4,     0,    18,     6,     0,    36,     8,     0,     9,    10,
      11,     0,    12,     0,     0,     0,     0,     0,     0,     0,
       0,    37,     0,    14,    15,   183,     0,     2,     0,     4,
       0,    18,     6,     0,    36,     8,     0,     9,    10,    11,
       0,    12,     0,     0,     0,     0,     0,     0,     0,     0,
      37,     0,    14,    15,   190,     0,     2,     0,     4,     0,
      18,     6,     0,    36,     8,     0,     9,    10,    11,     0,
      12,     0,     0,     0,     0,     0,     0,     0,     0,    37,
       0,    14,    15,     2,     0,     4,     0,     0,     6,    18,
      36,     8,     0,     9,    10,    11,     0,    12,     0,     0,
       0,     0,     0,     0,     0,     0,    37,     0,    14,    70,
       0,     2,     0,     4,     0,     0,    18,    83,     0,     8,
       0,     9,    10,    11,     0,    12,     0,     0,     0,     0,
       0,     0,     0,     0,    45,     0,    14,    15,     0,   105,
       2,     0,     4,     0,    18,     0,    83,     0,     8,     0,
       9,    10,    11,     0,    12,     0,     0,     0,     0,     0,
       0,     0,     0,    45,     0,    14,    15,     0,     2,     0,
       4,     0,     0,    18,    93,     0,     8,     0,     9,    10,
      11,     0,    12,     0,     0,     0,     0,     0,     2,     0,
       4,    45,     0,    14,    15,     0,     8,     0,     9,    10,
      11,    18,    12,     0,     0,     0,     0,     0,     0,     0,
       0,    45,     0,    14,    15,     2,   105,     4,     0,     0,
       2,    18,     4,     8,     0,     9,    10,    11,     8,    12,
       9,    10,    11,     0,    12,     0,     0,     0,    45,     0,
      14,    15,     2,   169,     4,    14,    15,     0,    18,     0,
       8,     0,     9,    10,    11,     0,    12,     0,     0,     0,
       0,     0,     0,     0,     0,    45,     0,    14,    15,     0,
       2,     0,     4,     0,     0,    18,    99,     2,     8,     4,
       9,    10,    11,   140,    12,     8,     0,     9,    10,    11,
       0,    12,     0,     0,     0,    14,    15,     0,     0,     0,
       0,     0,    14,    15
};

static const yytype_int16 yycheck[] =
{
       1,    36,     0,    48,     7,    37,     0,    19,    17,     8,
       6,    28,    83,    15,    17,    13,     3,    13,    61,    27,
      48,    12,    93,    15,    16,     3,    63,    72,    73,    74,
       3,    19,     3,    36,   105,     3,     3,    28,    46,    37,
      27,    37,    79,    21,    47,    82,     3,    50,    21,    45,
      58,    29,    14,    21,    21,    23,    22,    85,   101,   102,
      12,     7,    60,    98,    21,    27,    60,     0,    70,    27,
      36,    19,    70,    19,    32,   118,    28,    78,    70,    80,
      81,    39,   119,    21,    92,    24,     3,    88,    86,   124,
      99,    94,    86,   125,    32,    98,    99,    95,   169,    21,
      21,    23,   104,    19,     5,   137,     7,    32,    21,    10,
     106,    32,    13,    28,    15,    16,    17,    21,    19,    32,
      27,   124,   121,    20,   122,    32,    24,   125,    32,    30,
      31,   140,   167,   178,    27,    19,    29,   140,    32,   137,
     175,   149,    27,     3,    29,     5,    32,     7,    20,    28,
      10,    28,    12,    13,    37,    15,    16,    17,   156,    19,
     158,   162,    37,   161,   167,    32,    32,   161,    28,    26,
      30,    31,   175,    22,   172,   173,    25,    26,    38,    22,
      19,     3,    26,     5,    47,     7,   187,   185,    10,   142,
      12,    13,   141,    15,    16,    17,    -1,    19,    20,    21,
      22,    23,    24,    -1,    -1,    -1,    28,    -1,    30,    31,
      32,     3,    -1,     5,    -1,     7,    38,    -1,    10,    -1,
      12,    13,    -1,    15,    16,    17,    22,    19,    -1,    25,
      26,    -1,    -1,    -1,    -1,    -1,    28,    -1,    30,    31,
      -1,     4,     5,     6,     7,     8,    38,    10,    -1,    12,
      13,    -1,    15,    16,    17,    -1,    19,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    28,    29,    30,    31,    -1,
      -1,    34,    35,    -1,    -1,    38,     4,     5,     6,     7,
       8,    -1,    10,    -1,    12,    13,    -1,    15,    16,    17,
      -1,    19,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      28,    29,    30,    31,    -1,    -1,    34,    35,    -1,    -1,
      38,     4,     5,     6,     7,     8,    -1,    10,    -1,    12,
      13,    -1,    15,    16,    17,    -1,    19,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    28,    -1,    30,    31,    -1,
      -1,    34,    35,    -1,     5,    38,     7,    -1,    -1,    10,
      -1,    12,    13,    -1,    15,    16,    17,    -1,    19,    20,
      21,    22,    23,    24,    -1,    -1,    -1,    28,    -1,    30,
      31,    32,    -1,     5,    -1,     7,    -1,    38,    10,    -1,
      12,    13,    -1,    15,    16,    17,    -1,    19,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    28,    -1,    30,    31,
      32,    -1,     5,    -1,     7,    -1,    38,    10,    -1,    12,
      13,    -1,    15,    16,    17,    -1,    19,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    28,    -1,    30,    31,    32,
      -1,     5,    -1,     7,    -1,    38,    10,    -1,    12,    13,
      -1,    15,    16,    17,    -1,    19,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    28,    -1,    30,    31,    32,    -1,
       5,    -1,     7,    -1,    38,    10,    -1,    12,    13,    -1,
      15,    16,    17,    -1,    19,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    28,    -1,    30,    31,    32,    -1,     5,
      -1,     7,    -1,    38,    10,    -1,    12,    13,    -1,    15,
      16,    17,    -1,    19,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    28,    -1,    30,    31,    32,    -1,     5,    -1,
       7,    -1,    38,    10,    -1,    12,    13,    -1,    15,    16,
      17,    -1,    19,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    28,    -1,    30,    31,    32,    -1,     5,    -1,     7,
      -1,    38,    10,    -1,    12,    13,    -1,    15,    16,    17,
      -1,    19,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      28,    -1,    30,    31,    32,    -1,     5,    -1,     7,    -1,
      38,    10,    -1,    12,    13,    -1,    15,    16,    17,    -1,
      19,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    -1,    28,
      -1,    30,    31,     5,    -1,     7,    -1,    -1,    10,    38,
      12,    13,    -1,    15,    16,    17,    -1,    19,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    -1,    28,    -1,    30,    31,
      -1,     5,    -1,     7,    -1,    -1,    38,    11,    -1,    13,
      -1,    15,    16,    17,    -1,    19,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    28,    -1,    30,    31,    -1,    33,
       5,    -1,     7,    -1,    38,    -1,    11,    -1,    13,    -1,
      15,    16,    17,    -1,    19,    -1,    -1,    -1,    -1,    -1,
      -1,    -1,    -1,    28,    -1,    30,    31,    -1,     5,    -1,
       7,    -1,    -1,    38,    11,    -1,    13,    -1,    15,    16,
      17,    -1,    19,    -1,    -1,    -1,    -1,    -1,     5,    -1,
       7,    28,    -1,    30,    31,    -1,    13,    -1,    15,    16,
      17,    38,    19,    -1,    -1,    -1,    -1,    -1,    -1,    -1,
      -1,    28,    -1,    30,    31,     5,    33,     7,    -1,    -1,
       5,    38,     7,    13,    -1,    15,    16,    17,    13,    19,
      15,    16,    17,    -1,    19,    -1,    -1,    -1,    28,    -1,
      30,    31,     5,    33,     7,    30,    31,    -1,    38,    -1,
      13,    -1,    15,    16,    17,    -1,    19,    -1,    -1,    -1,
      -1,    -1,    -1,    -1,    -1,    28,    -1,    30,    31,    -1,
       5,    -1,     7,    -1,    -1,    38,    11,     5,    13,     7,
      15,    16,    17,    11,    19,    13,    -1,    15,    16,    17,
      -1,    19,    -1,    -1,    -1,    30,    31,    -1,    -1,    -1,
      -1,    -1,    30,    31
};

/* YYSTOS[STATE-NUM] -- The symbol kind of the accessing symbol of
   state STATE-NUM.  */
static const yytype_int8 yystos[] =
{
       0,     4,     5,     6,     7,     8,    10,    12,    13,    15,
      16,    17,    19,    28,    30,    31,    34,    35,    38,    41,
      42,    44,    47,    48,    49,    51,    53,    55,    57,    58,
      62,    63,    64,    67,    68,    70,    12,    28,    43,    48,
       7,    19,    19,    19,    19,    28,    55,    10,    52,    54,
      56,    57,    45,    46,    47,    59,    29,    41,    55,    60,
      69,    20,    21,    22,    23,    24,    32,    45,    49,    59,
      31,    49,    65,    66,    54,    28,     0,     3,    21,    22,
      25,    26,    24,    11,    58,    52,    69,     3,    27,    19,
       3,     3,    55,    11,    56,    28,    67,    68,    24,    11,
      57,    20,    23,    14,    27,    33,    27,    29,    29,    41,
      47,    32,    46,    32,    32,    51,    32,    32,    20,    22,
      32,    39,     3,    47,    36,    28,    68,    68,    68,    19,
      61,    48,    51,    48,    48,    51,    53,    28,    48,    53,
      11,    37,    37,    52,    54,    46,    46,    45,    53,    55,
      29,    32,    32,    32,    32,    59,     3,    47,     3,    50,
      52,    69,    26,    27,    29,    54,    62,    12,    63,    33,
      32,    47,     3,     3,    47,    22,    48,    19,    52,    53,
      32,    32,    47,    32,    47,     3,    52,    26,    32,    32,
      32,    47,    48,    32
};

/* YYR1[RULE-NUM] -- Symbol kind of the left-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr1[] =
{
       0,    40,    41,    41,    41,    41,    41,    41,    41,    42,
      43,    43,    44,    44,    44,    44,    45,    45,    46,    46,
      47,    47,    48,    48,    48,    49,    49,    50,    50,    51,
      51,    52,    52,    53,    53,    53,    53,    54,    54,    54,
      55,    55,    56,    56,    57,    57,    57,    57,    57,    57,
      57,    57,    57,    57,    57,    57,    57,    57,    57,    57,
      57,    57,    58,    58,    58,    59,    59,    60,    60,    61,
      61,    61,    61,    62,    62,    63,    63,    63,    64,    64,
      65,    65,    65,    65,    65,    65,    65,    66,    67,    68,
      68,    69,    69,    70
};

/* YYR2[RULE-NUM] -- Number of symbols on the right-hand side of rule RULE-NUM.  */
static const yytype_int8 yyr2[] =
{
       0,     2,     1,     1,     2,     1,     3,     3,     1,     3,
       3,     1,     1,     2,     2,     3,     3,     1,     3,     1,
       3,     1,     3,     3,     1,     3,     1,     3,     1,     3,
       1,     3,     1,     1,     4,     3,     1,     4,     3,     1,
       2,     1,     2,     1,     1,     1,     1,     1,     1,     3,
       3,     3,     4,     4,     4,     4,     3,     3,     2,     3,
       5,     3,     1,     3,     4,     3,     1,     5,     3,     5,
       3,     3,     1,     5,     1,     5,     3,     1,     3,     3,
       7,     6,     6,     5,     5,     6,     5,     3,     4,     3,
       2,     2,     1,     3
};


enum { YYENOMEM = -2 };

#define yyerrok         (yyerrstatus = 0)
#define yyclearin       (yychar = YYEMPTY)

#define YYACCEPT        goto yyacceptlab
#define YYABORT         goto yyabortlab
#define YYERROR         goto yyerrorlab
#define YYNOMEM         goto yyexhaustedlab


#define YYRECOVERING()  (!!yyerrstatus)

#define YYBACKUP(Token, Value)                                    \
  do                                                              \
    if (yychar == YYEMPTY)                                        \
      {                                                           \
        yychar = (Token);                                         \
        yylval = (Value);                                         \
        YYPOPSTACK (yylen);                                       \
        yystate = *yyssp;                                         \
        goto yybackup;                                            \
      }                                                           \
    else                                                          \
      {                                                           \
        yyerror (YY_("syntax error: cannot back up")); \
        YYERROR;                                                  \
      }                                                           \
  while (0)

/* Backward compatibility with an undocumented macro.
   Use YYerror or YYUNDEF. */
#define YYERRCODE YYUNDEF


/* Enable debugging if requested.  */
#if YYDEBUG

# ifndef YYFPRINTF
#  include <stdio.h> /* INFRINGES ON USER NAME SPACE */
#  define YYFPRINTF fprintf
# endif

# define YYDPRINTF(Args)                        \
do {                                            \
  if (yydebug)                                  \
    YYFPRINTF Args;                             \
} while (0)




# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)                    \
do {                                                                      \
  if (yydebug)                                                            \
    {                                                                     \
      YYFPRINTF (stderr, "%s ", Title);                                   \
      yy_symbol_print (stderr,                                            \
                  Kind, Value); \
      YYFPRINTF (stderr, "\n");                                           \
    }                                                                     \
} while (0)


/*-----------------------------------.
| Print this symbol's value on YYO.  |
`-----------------------------------*/

static void
yy_symbol_value_print (FILE *yyo,
                       yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep)
{
  FILE *yyoutput = yyo;
  YY_USE (yyoutput);
  if (!yyvaluep)
    return;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YY_USE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/*---------------------------.
| Print this symbol on YYO.  |
`---------------------------*/

static void
yy_symbol_print (FILE *yyo,
                 yysymbol_kind_t yykind, YYSTYPE const * const yyvaluep)
{
  YYFPRINTF (yyo, "%s %s (",
             yykind < YYNTOKENS ? "token" : "nterm", yysymbol_name (yykind));

  yy_symbol_value_print (yyo, yykind, yyvaluep);
  YYFPRINTF (yyo, ")");
}

/*------------------------------------------------------------------.
| yy_stack_print -- Print the state stack from its BOTTOM up to its |
| TOP (included).                                                   |
`------------------------------------------------------------------*/

static void
yy_stack_print (yy_state_t *yybottom, yy_state_t *yytop)
{
  YYFPRINTF (stderr, "Stack now");
  for (; yybottom <= yytop; yybottom++)
    {
      int yybot = *yybottom;
      YYFPRINTF (stderr, " %d", yybot);
    }
  YYFPRINTF (stderr, "\n");
}

# define YY_STACK_PRINT(Bottom, Top)                            \
do {                                                            \
  if (yydebug)                                                  \
    yy_stack_print ((Bottom), (Top));                           \
} while (0)


/*------------------------------------------------.
| Report that the YYRULE is going to be reduced.  |
`------------------------------------------------*/

static void
yy_reduce_print (yy_state_t *yyssp, YYSTYPE *yyvsp,
                 int yyrule)
{
  int yylno = yyrline[yyrule];
  int yynrhs = yyr2[yyrule];
  int yyi;
  YYFPRINTF (stderr, "Reducing stack by rule %d (line %d):\n",
             yyrule - 1, yylno);
  /* The symbols being reduced.  */
  for (yyi = 0; yyi < yynrhs; yyi++)
    {
      YYFPRINTF (stderr, "   $%d = ", yyi + 1);
      yy_symbol_print (stderr,
                       YY_ACCESSING_SYMBOL (+yyssp[yyi + 1 - yynrhs]),
                       &yyvsp[(yyi + 1) - (yynrhs)]);
      YYFPRINTF (stderr, "\n");
    }
}

# define YY_REDUCE_PRINT(Rule)          \
do {                                    \
  if (yydebug)                          \
    yy_reduce_print (yyssp, yyvsp, Rule); \
} while (0)

/* Nonzero means print parse trace.  It is left uninitialized so that
   multiple parsers can coexist.  */
int yydebug;
#else /* !YYDEBUG */
# define YYDPRINTF(Args) ((void) 0)
# define YY_SYMBOL_PRINT(Title, Kind, Value, Location)
# define YY_STACK_PRINT(Bottom, Top)
# define YY_REDUCE_PRINT(Rule)
#endif /* !YYDEBUG */


/* YYINITDEPTH -- initial size of the parser's stacks.  */
#ifndef YYINITDEPTH
# define YYINITDEPTH 200
#endif

/* YYMAXDEPTH -- maximum size the stacks can grow to (effective only
   if the built-in stack extension method is used).

   Do not make this value too large; the results are undefined if
   YYSTACK_ALLOC_MAXIMUM < YYSTACK_BYTES (YYMAXDEPTH)
   evaluated with infinite-precision integer arithmetic.  */

#ifndef YYMAXDEPTH
# define YYMAXDEPTH 10000
#endif






/*-----------------------------------------------.
| Release the memory associated to this symbol.  |
`-----------------------------------------------*/

static void
yydestruct (const char *yymsg,
            yysymbol_kind_t yykind, YYSTYPE *yyvaluep)
{
  YY_USE (yyvaluep);
  if (!yymsg)
    yymsg = "Deleting";
  YY_SYMBOL_PRINT (yymsg, yykind, yyvaluep, yylocationp);

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  YY_USE (yykind);
  YY_IGNORE_MAYBE_UNINITIALIZED_END
}


/* Lookahead token kind.  */
int yychar;

/* The semantic value of the lookahead symbol.  */
YYSTYPE yylval;
/* Number of syntax errors so far.  */
int yynerrs;




/*----------.
| yyparse.  |
`----------*/

int
yyparse (void)
{
    yy_state_fast_t yystate = 0;
    /* Number of tokens to shift before error messages enabled.  */
    int yyerrstatus = 0;

    /* Refer to the stacks through separate pointers, to allow yyoverflow
       to reallocate them elsewhere.  */

    /* Their size.  */
    YYPTRDIFF_T yystacksize = YYINITDEPTH;

    /* The state stack: array, bottom, top.  */
    yy_state_t yyssa[YYINITDEPTH];
    yy_state_t *yyss = yyssa;
    yy_state_t *yyssp = yyss;

    /* The semantic value stack: array, bottom, top.  */
    YYSTYPE yyvsa[YYINITDEPTH];
    YYSTYPE *yyvs = yyvsa;
    YYSTYPE *yyvsp = yyvs;

  int yyn;
  /* The return value of yyparse.  */
  int yyresult;
  /* Lookahead symbol kind.  */
  yysymbol_kind_t yytoken = YYSYMBOL_YYEMPTY;
  /* The variables used to return semantic value and location from the
     action routines.  */
  YYSTYPE yyval;



#define YYPOPSTACK(N)   (yyvsp -= (N), yyssp -= (N))

  /* The number of symbols on the RHS of the reduced rule.
     Keep to zero when no symbol should be popped.  */
  int yylen = 0;

  YYDPRINTF ((stderr, "Starting parse\n"));

  yychar = YYEMPTY; /* Cause a token to be read.  */

  goto yysetstate;


/*------------------------------------------------------------.
| yynewstate -- push a new state, which is found in yystate.  |
`------------------------------------------------------------*/
yynewstate:
  /* In all cases, when you get here, the value and location stacks
     have just been pushed.  So pushing a state here evens the stacks.  */
  yyssp++;


/*--------------------------------------------------------------------.
| yysetstate -- set current state (the top of the stack) to yystate.  |
`--------------------------------------------------------------------*/
yysetstate:
  YYDPRINTF ((stderr, "Entering state %d\n", yystate));
  YY_ASSERT (0 <= yystate && yystate < YYNSTATES);
  YY_IGNORE_USELESS_CAST_BEGIN
  *yyssp = YY_CAST (yy_state_t, yystate);
  YY_IGNORE_USELESS_CAST_END
  YY_STACK_PRINT (yyss, yyssp);

  if (yyss + yystacksize - 1 <= yyssp)
#if !defined yyoverflow && !defined YYSTACK_RELOCATE
    YYNOMEM;
#else
    {
      /* Get the current used size of the three stacks, in elements.  */
      YYPTRDIFF_T yysize = yyssp - yyss + 1;

# if defined yyoverflow
      {
        /* Give user a chance to reallocate the stack.  Use copies of
           these so that the &'s don't force the real ones into
           memory.  */
        yy_state_t *yyss1 = yyss;
        YYSTYPE *yyvs1 = yyvs;

        /* Each stack pointer address is followed by the size of the
           data in use in that stack, in bytes.  This used to be a
           conditional around just the two extra args, but that might
           be undefined if yyoverflow is a macro.  */
        yyoverflow (YY_("memory exhausted"),
                    &yyss1, yysize * YYSIZEOF (*yyssp),
                    &yyvs1, yysize * YYSIZEOF (*yyvsp),
                    &yystacksize);
        yyss = yyss1;
        yyvs = yyvs1;
      }
# else /* defined YYSTACK_RELOCATE */
      /* Extend the stack our own way.  */
      if (YYMAXDEPTH <= yystacksize)
        YYNOMEM;
      yystacksize *= 2;
      if (YYMAXDEPTH < yystacksize)
        yystacksize = YYMAXDEPTH;

      {
        yy_state_t *yyss1 = yyss;
        union yyalloc *yyptr =
          YY_CAST (union yyalloc *,
                   YYSTACK_ALLOC (YY_CAST (YYSIZE_T, YYSTACK_BYTES (yystacksize))));
        if (! yyptr)
          YYNOMEM;
        YYSTACK_RELOCATE (yyss_alloc, yyss);
        YYSTACK_RELOCATE (yyvs_alloc, yyvs);
#  undef YYSTACK_RELOCATE
        if (yyss1 != yyssa)
          YYSTACK_FREE (yyss1);
      }
# endif

      yyssp = yyss + yysize - 1;
      yyvsp = yyvs + yysize - 1;

      YY_IGNORE_USELESS_CAST_BEGIN
      YYDPRINTF ((stderr, "Stack size increased to %ld\n",
                  YY_CAST (long, yystacksize)));
      YY_IGNORE_USELESS_CAST_END

      if (yyss + yystacksize - 1 <= yyssp)
        YYABORT;
    }
#endif /* !defined yyoverflow && !defined YYSTACK_RELOCATE */


  if (yystate == YYFINAL)
    YYACCEPT;

  goto yybackup;


/*-----------.
| yybackup.  |
`-----------*/
yybackup:
  /* Do appropriate processing given the current state.  Read a
     lookahead token if we need one and don't already have one.  */

  /* First try to decide what to do without reference to lookahead token.  */
  yyn = yypact[yystate];
  if (yypact_value_is_default (yyn))
    goto yydefault;

  /* Not known => get a lookahead token if don't already have one.  */

  /* YYCHAR is either empty, or end-of-input, or a valid lookahead.  */
  if (yychar == YYEMPTY)
    {
      YYDPRINTF ((stderr, "Reading a token\n"));
      yychar = yylex ();
    }

  if (yychar <= YYEOF)
    {
      yychar = YYEOF;
      yytoken = YYSYMBOL_YYEOF;
      YYDPRINTF ((stderr, "Now at end of input.\n"));
    }
  else if (yychar == YYerror)
    {
      /* The scanner already issued an error message, process directly
         to error recovery.  But do not keep the error token as
         lookahead, it is too special and may lead us to an endless
         loop in error recovery. */
      yychar = YYUNDEF;
      yytoken = YYSYMBOL_YYerror;
      goto yyerrlab1;
    }
  else
    {
      yytoken = YYTRANSLATE (yychar);
      YY_SYMBOL_PRINT ("Next token is", yytoken, &yylval, &yylloc);
    }

  /* If the proper action on seeing token YYTOKEN is to reduce or to
     detect an error, take that action.  */
  yyn += yytoken;
  if (yyn < 0 || YYLAST < yyn || yycheck[yyn] != yytoken)
    goto yydefault;
  yyn = yytable[yyn];
  if (yyn <= 0)
    {
      if (yytable_value_is_error (yyn))
        goto yyerrlab;
      yyn = -yyn;
      goto yyreduce;
    }

  /* Count tokens shifted since error; after three, turn off error
     status.  */
  if (yyerrstatus)
    yyerrstatus--;

  /* Shift the lookahead token.  */
  YY_SYMBOL_PRINT ("Shifting", yytoken, &yylval, &yylloc);
  yystate = yyn;
  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END

  /* Discard the shifted token.  */
  yychar = YYEMPTY;
  goto yynewstate;


/*-----------------------------------------------------------.
| yydefault -- do the default action for the current state.  |
`-----------------------------------------------------------*/
yydefault:
  yyn = yydefact[yystate];
  if (yyn == 0)
    goto yyerrlab;
  goto yyreduce;


/*-----------------------------.
| yyreduce -- do a reduction.  |
`-----------------------------*/
yyreduce:
  /* yyn is the number of a rule to reduce with.  */
  yylen = yyr2[yyn];

  /* If YYLEN is nonzero, implement the default value of the action:
     '$$ = $1'.

     Otherwise, the following line sets YYVAL to garbage.
     This behavior is undocumented and Bison
     users should not rely upon it.  Assigning to YYVAL
     unconditionally makes the parser a bit smaller, and it avoids a
     GCC warning that YYVAL may be used uninitialized.  */
  yyval = yyvsp[1-yylen];


  YY_REDUCE_PRINT (yyn);
  switch (yyn)
    {

#line 1442 "nothing.tab.c"

      default: break;
    }
  /* User semantic actions sometimes alter yychar, and that requires
     that yytoken be updated with the new translation.  We take the
     approach of translating immediately before every use of yytoken.
     One alternative is translating here after every semantic action,
     but that translation would be missed if the semantic action invokes
     YYABORT, YYACCEPT, or YYERROR immediately after altering yychar or
     if it invokes YYBACKUP.  In the case of YYABORT or YYACCEPT, an
     incorrect destructor might then be invoked immediately.  In the
     case of YYERROR or YYBACKUP, subsequent parser actions might lead
     to an incorrect destructor call or verbose syntax error message
     before the lookahead is translated.  */
  YY_SYMBOL_PRINT ("-> $$ =", YY_CAST (yysymbol_kind_t, yyr1[yyn]), &yyval, &yyloc);

  YYPOPSTACK (yylen);
  yylen = 0;

  *++yyvsp = yyval;

  /* Now 'shift' the result of the reduction.  Determine what state
     that goes to, based on the state we popped back to and the rule
     number reduced by.  */
  {
    const int yylhs = yyr1[yyn] - YYNTOKENS;
    const int yyi = yypgoto[yylhs] + *yyssp;
    yystate = (0 <= yyi && yyi <= YYLAST && yycheck[yyi] == *yyssp
               ? yytable[yyi]
               : yydefgoto[yylhs]);
  }

  goto yynewstate;


/*--------------------------------------.
| yyerrlab -- here on detecting error.  |
`--------------------------------------*/
yyerrlab:
  /* Make sure we have latest lookahead translation.  See comments at
     user semantic actions for why this is necessary.  */
  yytoken = yychar == YYEMPTY ? YYSYMBOL_YYEMPTY : YYTRANSLATE (yychar);
  /* If not already recovering from an error, report this error.  */
  if (!yyerrstatus)
    {
      ++yynerrs;
      yyerror (YY_("syntax error"));
    }

  if (yyerrstatus == 3)
    {
      /* If just tried and failed to reuse lookahead token after an
         error, discard it.  */

      if (yychar <= YYEOF)
        {
          /* Return failure if at end of input.  */
          if (yychar == YYEOF)
            YYABORT;
        }
      else
        {
          yydestruct ("Error: discarding",
                      yytoken, &yylval);
          yychar = YYEMPTY;
        }
    }

  /* Else will try to reuse lookahead token after shifting the error
     token.  */
  goto yyerrlab1;


/*---------------------------------------------------.
| yyerrorlab -- error raised explicitly by YYERROR.  |
`---------------------------------------------------*/
yyerrorlab:
  /* Pacify compilers when the user code never invokes YYERROR and the
     label yyerrorlab therefore never appears in user code.  */
  if (0)
    YYERROR;
  ++yynerrs;

  /* Do not reclaim the symbols of the rule whose action triggered
     this YYERROR.  */
  YYPOPSTACK (yylen);
  yylen = 0;
  YY_STACK_PRINT (yyss, yyssp);
  yystate = *yyssp;
  goto yyerrlab1;


/*-------------------------------------------------------------.
| yyerrlab1 -- common code for both syntax error and YYERROR.  |
`-------------------------------------------------------------*/
yyerrlab1:
  yyerrstatus = 3;      /* Each real token shifted decrements this.  */

  /* Pop stack until we find a state that shifts the error token.  */
  for (;;)
    {
      yyn = yypact[yystate];
      if (!yypact_value_is_default (yyn))
        {
          yyn += YYSYMBOL_YYerror;
          if (0 <= yyn && yyn <= YYLAST && yycheck[yyn] == YYSYMBOL_YYerror)
            {
              yyn = yytable[yyn];
              if (0 < yyn)
                break;
            }
        }

      /* Pop the current state because it cannot handle the error token.  */
      if (yyssp == yyss)
        YYABORT;


      yydestruct ("Error: popping",
                  YY_ACCESSING_SYMBOL (yystate), yyvsp);
      YYPOPSTACK (1);
      yystate = *yyssp;
      YY_STACK_PRINT (yyss, yyssp);
    }

  YY_IGNORE_MAYBE_UNINITIALIZED_BEGIN
  *++yyvsp = yylval;
  YY_IGNORE_MAYBE_UNINITIALIZED_END


  /* Shift the error token.  */
  YY_SYMBOL_PRINT ("Shifting", YY_ACCESSING_SYMBOL (yyn), yyvsp, yylsp);

  yystate = yyn;
  goto yynewstate;


/*-------------------------------------.
| yyacceptlab -- YYACCEPT comes here.  |
`-------------------------------------*/
yyacceptlab:
  yyresult = 0;
  goto yyreturnlab;


/*-----------------------------------.
| yyabortlab -- YYABORT comes here.  |
`-----------------------------------*/
yyabortlab:
  yyresult = 1;
  goto yyreturnlab;


/*-----------------------------------------------------------.
| yyexhaustedlab -- YYNOMEM (memory exhaustion) comes here.  |
`-----------------------------------------------------------*/
yyexhaustedlab:
  yyerror (YY_("memory exhausted"));
  yyresult = 2;
  goto yyreturnlab;


/*----------------------------------------------------------.
| yyreturnlab -- parsing is finished, clean up and return.  |
`----------------------------------------------------------*/
yyreturnlab:
  if (yychar != YYEMPTY)
    {
      /* Make sure we have latest lookahead translation.  See comments at
         user semantic actions for why this is necessary.  */
      yytoken = YYTRANSLATE (yychar);
      yydestruct ("Cleanup: discarding lookahead",
                  yytoken, &yylval);
    }
  /* Do not reclaim the symbols of the rule whose action triggered
     this YYABORT or YYACCEPT.  */
  YYPOPSTACK (yylen);
  YY_STACK_PRINT (yyss, yyssp);
  while (yyssp != yyss)
    {
      yydestruct ("Cleanup: popping",
                  YY_ACCESSING_SYMBOL (+*yyssp), yyvsp);
      YYPOPSTACK (1);
    }
#ifndef yyoverflow
  if (yyss != yyssa)
    YYSTACK_FREE (yyss);
#endif

  return yyresult;
}

#line 136 "nothing.y"


// [A {}]
