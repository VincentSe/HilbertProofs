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
	      printf("Parsing file %s\n", fileName);
	      asts[numberFound] = make_folAST(fileName);
	      numberFound++;
	    }
	}
      closedir(d);
    }
  asts[numberFound] = (struct folAST*)0;
  return numberFound;
}

void free_first_asts(struct folAST** asts, unsigned int count)
{
  for (int j = 0; j < count; j++)
    folAST_free(asts[j]);  
}

int main(int argc, char** argv)
{
  struct folAST* asts[16];
  unsigned int astCount = 0, i;
  if (argc == 1)
    astCount = list_fol_files("math", /*out*/asts);
  else
    {
      // Assume all arguments are file names
      for (astCount = 0; astCount<argc-1; astCount++)
	asts[astCount] = make_folAST(argv[astCount+1]);
    }
  asts[astCount] = (struct folAST*)0;

  for (i = 0; i < astCount; i++)
    if (parse_fo_formulas(asts[i]) != 0) // 0 means bison succeeded
      {
	printf("parsing failure\n");
	free_first_asts(asts, astCount);
	return 1;
      }

  unsigned int astSort[16];
  unsigned char success = resolve_extends(/*out*/asts, /*out*/astSort);

  fflush(stdout); // in case the destructors below crash

  // Destroy asts in reverse order of dependencies.
  // Even in case of error, resolve_extends must cleanup what it did
  // so that the following destruction loop works :
  for (int i = astCount-1; i >= 0; i--)
    folAST_free(asts[astSort[i]]);
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
