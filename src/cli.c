/**
   The command-line interface of the proof checker.
 */

#include <stdio.h>
#include "folAST.h"
#include <dirent.h>
#include <string.h>

// make command :
// D:\msys64\mingw64\bin\mingw32-make.exe -C d:/projects/HilbertProofs -k build
// D:\msys64\mingw64\bin\gdb.exe bin\proveMath.exe

unsigned int list_fol_files(const char* dirPath,
			    /*out*/ struct folAST** asts)
{
  struct dirent *dir;
  DIR* d = opendir(dirPath);
  unsigned int numberFound = 0;
  char fileName[128];
  if (d)
    {
      while ((dir = readdir(d)))
	{
	  char* endFile = strstr(dir->d_name, ".fol");
	  if (endFile && !endFile[4])
	    {
	      sprintf(fileName, "%s/%s", dirPath, dir->d_name);
	      asts[numberFound] = make_folAST(fileName);
	      numberFound++;
	    }
	}
      closedir(d);
    }
  asts[numberFound] = (struct folAST*)0;
  return numberFound;
}

int main(int argc, char** argv)
{
  struct folAST* asts[16];
  if (argc == 1)
    {
      asts[0] = make_folAST("math/Tautologies.fol");
      asts[1] = make_folAST("math/ZFC.fol"); 
      asts[2] = make_folAST("math/Ordinals.fol");
      asts[3] = (struct folAST*)0;
      //list_fol_files("math", /*out*/asts); TODO
    }
  else
    {
      // Assume all arguments are file names
      int i;
      for (i = 1; i<argc; i++)
	{
	  asts[i-1] = make_folAST(argv[i]);
	}
      asts[i-1] = (struct folAST*)0;
    }

  struct folAST** ast = asts;
  while (*ast && (parse_fo_formulas(*ast) == 0)) // 0 means success in bison
    ast++;

  unsigned char success = 1;
  if (*ast // parsing failed
      || !resolve_extends(/*out*/asts))
    success = 0;

  // Destroy asts in reverse order of dependencies
  while (ast >= asts)
    {
      folAST_free(*ast);
      ast--;
    }
  return !success;
}


/* int current_memory() */
/* { */
/*   char * buffer = 0; */
/*   char str[128]; */
/*   long length; */
/*   int memory = 0; */
/*   FILE * f = fopen("/proc/self/status", "r"); */
/*   if (f) */
/*     { */
/*       while (fscanf(f, "%s", str)!=EOF) */
/* 	{ */
/* 	  if (strcmp("VmSize:", str) == 0) */
/* 	    { */
/* 	      fscanf(f, "%s", str); */
/* 	      memory = atoi(str); */
/* 	    } */
/* 	} */
/*       fclose(f); */
/*     } */
/*   /\* else *\/ */
/*   /\* 	printf("Cannot open memory file\n"); *\/ */

/*   return memory; */
/* } */

/* int test_memory_leak() */
/* { */
/*   int toto; */
/*   for (int i = 0; i<1000; i++) */
/*     { */
/*       struct folAST ast; */
/*       ast.file = "math/zfc.fol"; */
/*       parse_fo_formulas(&ast); */
/*       const int memory = current_memory(); */
/*       void deleter(void* t) { formula_free(t); } */
/*       tdestroy(ast.operators, deleter); */
/*       proof_list_free(ast.proofs); */

/*       if (i == 0) */
/* 	printf("After first pass %d kb\n", memory); */
/*     } */

/*   const int memory = current_memory(); */
/*   printf("After many passes %d kb\n", memory); */
/* } */
