import com.alibaba.fastjson.JSON;
import com.alibaba.fastjson.TypeReference;
import org.logicng.datastructures.Assignment;
import org.logicng.formulas.Formula;
import org.logicng.formulas.FormulaFactory;
import org.logicng.formulas.Variable;
import org.logicng.solvers.MiniSat;
import org.logicng.solvers.SATSolver;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

class NonexistantDependencyException extends Exception {
    public NonexistantDependencyException() {
        super();
    }
}

class Package {
  private String name;
  private String version;
  private Integer size;
  private List<List<String>> depends = new ArrayList<>();
  private List<String> conflicts = new ArrayList<>();

  public String getName() { return name; }
  public String getVersion() { return version; }
  public Integer getSize() { return size; }
  public List<List<String>> getDepends() { return depends; }
  public List<String> getConflicts() { return conflicts; }
  public void setName(String name) { this.name = name; }
  public void setVersion(String version) { this.version = version; }
  public void setSize(Integer size) { this.size = size; }
  public void setDepends(List<List<String>> depends) { this.depends = depends; }
  public void setConflicts(List<String> conflicts) { this.conflicts = conflicts; }
}

public class Main {
  private static HashMap<String, Package> stringToPackageMappings = new HashMap<>();

  private static HashMap<String, Set<Package>> getPackageVersions(List<Package> repo) {
    HashMap<String, Set<Package>> packageVersions = new HashMap<>();

    for(Package p : repo) {
      stringToPackageMappings.put(p.getName() + "="+ p.getVersion(), p);
      Set<Package> versions = packageVersions.getOrDefault(p.getName(), new HashSet<>());
      versions.add(p);
      packageVersions.put(p.getName(), versions);
    }

    return packageVersions;
  }

  public static void main(String[] args) throws IOException {
    TypeReference<List<Package>> repoType = new TypeReference<List<Package>>() {};
    List<Package> repo = JSON.parseObject(readFile(args[0]), repoType);
    TypeReference<List<String>> strListType = new TypeReference<List<String>>() {};
    List<String> initial = JSON.parseObject(readFile(args[1]), strListType);
    List<String> constraintsString = JSON.parseObject(readFile(args[2]), strListType);

    HashMap<String, Set<Package>> packageVersions = Main.getPackageVersions(repo);

    Set<Set<Package>> finalInstalled = new HashSet<>();
    Set<Package> finalDoNotInstall = new HashSet<>();

    for(String c : constraintsString) {
      Boolean installed;

      if(c.charAt(0) == '+') {
        installed = true;
      } else {
        installed = false;
      }

      String packageName = "";

      Predicate<Package> versionPredicate;
      if(c.indexOf('>') > -1) {
        if(c.indexOf('=') > -1) {
          String versionNumber = stripVersionNumber(c.substring(c.indexOf('=') + 1));
          versionPredicate = (Package p) -> stripVersionNumber(p.getVersion()).compareTo(versionNumber) >= 0;
        } else {
          String versionNumber = stripVersionNumber(c.substring(c.indexOf('>') + 1));
          versionPredicate = (Package p) -> stripVersionNumber(p.getVersion()).compareTo(versionNumber) > 0;
        }
        packageName = c.substring(1, c.indexOf('>'));
      } else if(c.indexOf('<') > -1) {
        if(c.indexOf('=') > -1) {
          String versionNumber = stripVersionNumber(c.substring(c.indexOf('=') + 1));
          versionPredicate = (Package p) -> stripVersionNumber(p.getVersion()).compareTo(versionNumber) <= 0;
        } else {
          String versionNumber = stripVersionNumber(c.substring(c.indexOf('>') + 1));
          versionPredicate = (Package p) -> stripVersionNumber(p.getVersion()).compareTo(versionNumber) < 0;
        }
        packageName = c.substring(1, c.indexOf('<'));
      } else if(c.indexOf('=') > -1) {
        String versionNumber = stripVersionNumber(c.substring(c.indexOf('=') + 1));
        versionPredicate = (Package p) -> stripVersionNumber(p.getVersion()).equals(versionNumber);
        packageName = c.substring(1, c.indexOf('='));
      } else {
        versionPredicate = (Package p) -> true;
        packageName = c.substring(1);
      }

      Set<Package> matchingPackages = packageVersions.get(packageName).stream().filter(versionPredicate).collect(Collectors.toSet());
      if(installed) finalInstalled.add(matchingPackages);
      else finalDoNotInstall.addAll(matchingPackages);
    }

    Set<Package> initialPackages = initial.stream().map(nextPackageString -> stringToPackageMappings.get(nextPackageString)).collect(Collectors.toSet());

//    finalInstalled = removeInitiallySatisfiedConstraints(initialPackages, finalInstalled, finalDoNotInstall);

    List<Assignment> validModels = getValidStates(repo, finalInstalled, finalDoNotInstall, packageVersions);

    Set<Package> lowestScoreInstalls = null;
    Set<Package> lowestScoreDoNotInstalls = null;
    Long lowestScore = Long.MAX_VALUE;
    if(validModels.isEmpty()) {
        System.out.println("[]");
        return;
    }
    for(Assignment nextModel : validModels) {
        Set<Package> install = nextModel.positiveLiterals().stream().map(v -> stringToPackageMappings.get(v.name())).collect(Collectors.toSet());
        Set<Package> doNotInstall = nextModel.negativeVariables().stream().map(v -> stringToPackageMappings.get(v.name())).collect(Collectors.toSet());

        Long score = calculateModelScore(install, doNotInstall, initialPackages);

        if(score <= lowestScore) {
            lowestScoreInstalls = install;
            lowestScoreDoNotInstalls = doNotInstall;
            lowestScore = score;
        }
    }


    Set<Package> uninstalls = getSetIntersection(lowestScoreDoNotInstalls, initialPackages);
    initialPackages.removeAll(uninstalls);

    LinkedList<Package> installs = getOrderOfInstallsSlow(initialPackages, lowestScoreInstalls, packageVersions);

    System.out.print('[');
    String actionString = "";
    for(Package nextUninstall : uninstalls) {
        actionString += constructStringForInstall(nextUninstall, false) + ',';
    }

    for(Package nextInstall : installs) {
        if(!initialPackages.contains(nextInstall)) actionString += constructStringForInstall(nextInstall, true) + ',';
    }

    if(actionString.indexOf(',') != -1) actionString = actionString.substring(0, actionString.length() - 1);
    System.out.print(actionString);
    System.out.println(']');
  }

  private static Set<Set<Package>> removeInitiallySatisfiedConstraints(Set<Package> initial, Set<Set<Package>> installConstraints, Set<Package> doNotInstallConstraints) {
      Set<Set<Package>> result = new HashSet<>();
    for(Set<Package> nextInstallConstraintAnd : installConstraints) {
        boolean definitelySatisfied = true;
        for(Package nextInstallConstraintOr : nextInstallConstraintAnd) {
            if(!initial.contains(nextInstallConstraintOr)) {
                definitelySatisfied = false;
                break;
            }
        }

        if(!definitelySatisfied) {
            result.add(nextInstallConstraintAnd);
        }
    }

    return result;
  }

  private static LinkedList getOrderOfInstallsSlow(Set<Package> initial, Set<Package> install, Map<String, Set<Package>> packageVersions) {
      LinkedList<Package> packageQueue = new LinkedList<>(install);

      LinkedList<Package> result = new LinkedList<>(initial);

      while(!packageQueue.isEmpty()) {
          Package p = packageQueue.pollFirst();

          if(hasUnmetDependencies(p, result, packageVersions)) {
              packageQueue.addLast(p);
          } else {
              result.add(p);
          }
      }

      return result;
  }

  private static boolean hasUnmetDependencies(Package p, List<Package> installed,  Map<String, Set<Package>> packageVersions) {
      List<List<String>> packageDependenciesRaw = p.getDepends();

      for(List<String> nextDependencyRawAnd : packageDependenciesRaw) {
          boolean satisfied = false;

          Set<Set<Package>> nextDependencyAnd = getPackagesFromString(nextDependencyRawAnd, packageVersions);

          for(Set<Package> nextDependencyOrOuter : nextDependencyAnd) {
              boolean found = false;

              for(Package nextDependencyOrInner : nextDependencyOrOuter) {
                  if(installed.contains(nextDependencyOrInner)) {
                      found = true;
                      break;
                  }
              }

              if(found) {
                  satisfied = true;
                  break;
              }
          }

          if(!satisfied) {
              return true;
          }
      }

      return false;
  }

  private static LinkedHashSet<Package> getOrderOfInstallsFastButNotWorking(Set<Package> install, Set<Package> doNotInstall, Map<String, Set<Package>> packageVersions) {
      HashMap<Package, List<Package>> incomingEdges = new HashMap<>();
      HashMap<Package, List<Package>> outgoingEdges = new HashMap<>();

      Stack<Package> noIncomingEdges = new Stack<>();

      LinkedList<Package> result = new LinkedList<>();

      for(Package nextPackageToInstall : install) {
          List<List<String>> rawDependencies = nextPackageToInstall.getDepends();

          Set<Package> validDependenciesAnd = new HashSet<>();

          for(List<String> nextRawDependencyAnd : rawDependencies) {
                Set<Set<Package>> dependenciesOrOuter = getPackagesFromString(nextRawDependencyAnd, packageVersions);

                LinkedList<Package> validDependenciesOrOuter = new LinkedList<>();

                for(Set<Package> nextDependencyOrOuter : dependenciesOrOuter) {
                    LinkedList<Package> validDependenciesOrInner = new LinkedList<>();

                    for(Package nextDependencyOrInner : nextDependencyOrOuter) {
                        if(install.contains(nextDependencyOrInner) && !doNotInstall.contains(nextDependencyOrInner)) validDependenciesOrInner.add(nextDependencyOrInner); // we can stop as soon as we find one
                    }

                    validDependenciesOrOuter.addAll(validDependenciesOrInner); // we only care about one that matches. we can stop as soon as we find one
                }

                validDependenciesAnd.add(validDependenciesOrOuter.stream().filter(nextDependency -> incomingEdges.get(nextDependency) == null || !incomingEdges.get(nextDependency).contains(nextPackageToInstall)).findFirst().get());
          }

          List<Package> previousIncomingEdges = incomingEdges.getOrDefault(nextPackageToInstall, new LinkedList<>());
          previousIncomingEdges.addAll(validDependenciesAnd);
          incomingEdges.put(nextPackageToInstall, previousIncomingEdges);

          if(previousIncomingEdges.isEmpty()) noIncomingEdges.push(nextPackageToInstall);

          for(Package nextValidDependencyAnd : validDependenciesAnd) {
              List<Package> previousOutgoingEdges = outgoingEdges.getOrDefault(nextValidDependencyAnd, new LinkedList<>());
              previousOutgoingEdges.add(nextPackageToInstall);
              outgoingEdges.put(nextValidDependencyAnd, previousOutgoingEdges);
          }
      }

      // do kahns BITCH
      while(!noIncomingEdges.isEmpty()) {
          Package n = noIncomingEdges.pop();
          result.push(n);

          List<Package> currOutgoingEdges = outgoingEdges.getOrDefault(n, new LinkedList<>());
          for(Package m : currOutgoingEdges) {
              List<Package> currIncomingEdges = incomingEdges.get(m);
              currIncomingEdges.remove(n);
              incomingEdges.put(m, currIncomingEdges);

              if(currIncomingEdges.isEmpty()) {
                  noIncomingEdges.push(m);
              }
          }
      }


      Collections.reverse(result); // need to avoid creating a circular guy, as happens in seen-6
      return new LinkedHashSet<>(result);
  }

  private static String constructStringForInstall(Package p, boolean install) {
      StringBuilder s = new StringBuilder();
      s.append('"');
      if(install) s.append("+");
      else s.append('-');

      s.append(p.getName());
      s.append('=');
      s.append(p.getVersion());
      s.append('"');

      return s.toString();
  }

  private static Long calculateModelScore(Set<Package> install, Set<Package> doNotInstall, Set<Package> initial) {
      Long score = 0L;

      for(Package installed : install) {
          if(!initial.contains(installed)) score += installed.getSize();
      }

      Set<Package> doNotInstallAndInitialIntersection = new HashSet<>(doNotInstall);
      doNotInstallAndInitialIntersection.retainAll(initial);

      score += 1000000 * (getSetIntersection(doNotInstall, initial).size());

      return score;
  }

  private static Set<Package> getSetIntersection(Set<Package> set1, Set<Package> set2) {
      Set<Package> doNotInstallAndInitialIntersection = new HashSet<>(set1);
      doNotInstallAndInitialIntersection.retainAll(set2);

      return doNotInstallAndInitialIntersection;
  }

  /**
   * Gets a list of valid states using a SAT solver.
   * @param packages
   * @return
   */
  private static List<Assignment> getValidStates(List<Package> repo, Set<Set<Package>> packages, Set<Package> doNotWantPackages, Map<String, Set<Package>> packageVersions) {
    final FormulaFactory f = new FormulaFactory();

    Formula packageDefinitionsFormula = generatePackageDefinitionsFormula(repo, f, packageVersions); // idea: generate package dependencies only for packages we might need

    Formula mustNotInstall = negateAllAndGenerateAnd(doNotWantPackages, f);

    List<Formula> mustInstallAndFormulas = new LinkedList<>();

    for(Set<Package> nextMustInstallAndGroup : packages) {
        List<Formula> mustInstallOrFormulas = new LinkedList<>();

        for(Package nextMustInstallOr : nextMustInstallAndGroup) {
            mustInstallOrFormulas.add(getPackageVariable(nextMustInstallOr, f));
        }

        Formula mustInstallOrFormula = f.or(mustInstallOrFormulas);
        mustInstallAndFormulas.add(mustInstallOrFormula);
    }

    Formula mustInstallAndFormula = f.and(mustInstallAndFormulas);

    Formula finalFormula = f.and(packageDefinitionsFormula, mustNotInstall, mustInstallAndFormula);

    final SATSolver miniSat = MiniSat.miniSat(f);
    miniSat.add(finalFormula);
    miniSat.sat();

    List<Assignment> possibleModels = miniSat.enumerateAllModels(); // get OutOfMemoryError here. use a list of variables that's filtered on ones we're definitely not using?
    return possibleModels;
  }

    /**
     * Recursive function that expands the package into its dependencies
     * @param p the current package that we're expanding
     * @param f
     * @param packageVersions
     * @return
     */
  private static Formula getPackageDependenciesFormula(Package p, FormulaFactory f, Map<String, Set<Package>> packageVersions) throws NonexistantDependencyException {
      List<List<String>> thisPackageDependenciesRaw = p.getDepends();

      List<Formula> dependenciesFormulas = new LinkedList<>();

      for(List<String> nextPackageDependencyRaw : thisPackageDependenciesRaw) {
          Set<Set<Package>> nextPackageDependencies = null;
          nextPackageDependencies = getPackagesFromStringWithException(nextPackageDependencyRaw, packageVersions);

          List<Formula> dependencyOuterOr = new LinkedList<>();

          for(Set<Package> nextPackageDependencyAnd : nextPackageDependencies) {
              List<Formula> dependencyInnerOr = new LinkedList<>();
              for(Package nextPackageDependencyOr : nextPackageDependencyAnd) {
                  dependencyInnerOr.add(getPackageVariable(nextPackageDependencyOr, f));
              }
              Formula innerOrFormula = f.or(dependencyInnerOr);
              dependencyOuterOr.add(innerOrFormula);
          }

          Formula outerOrFormula = f.or(dependencyOuterOr);
          dependenciesFormulas.add(outerOrFormula);
      }


      Formula dependenciesFormula = f.and(dependenciesFormulas);
      return dependenciesFormula;
  }

  private static Formula getPackageConflictsFormula(Package p, FormulaFactory f, Map<String, Set<Package>> packageVersions) {
      List<Formula> conflictsFormulas = new LinkedList<>();

      List<String> packageConflictsRaw = p.getConflicts();

      Set<Set<Package>> packageConflicts = getPackagesFromString(packageConflictsRaw, packageVersions);

      for(Set<Package> nextPackageConflictGroup : packageConflicts) {
          conflictsFormulas.add(negateAllAndGenerateAnd(nextPackageConflictGroup, f));
      }

      return f.and(conflictsFormulas);
  }

  private static Variable getPackageVariable(Package p, FormulaFactory f) {
      String variableName = p.getName() + "=" + p.getVersion();
      return f.variable(variableName);
  }



    /**
     * Extracts a set of packages from a string of package dependencies or conflicts, throws an exception if a package has dependencies that don't exist in the repository
     * @param packageString
     * @param packageVersions
     * @return
     */
    private static Set<Set<Package>> getPackagesFromString(List<String> packageString, Map<String, Set<Package>> packageVersions) {
        Set<Set<Package>> resultPackages = new HashSet<>();

        for(String c : packageString) {
            String packageName = "";

            Predicate<Package> versionPredicate;
            if(c.indexOf('>') > -1) {
                if(c.indexOf('=') > -1) {
                    String versionNumber = c.substring(c.indexOf('=') + 1);
                    versionPredicate = (Package p) -> p.getVersion().compareTo(versionNumber) >= 0;
                } else {
                    String versionNumber = c.substring(c.indexOf('>') + 1);
                    versionPredicate = (Package p) -> p.getVersion().compareTo(versionNumber) > 0;
                }
                packageName = c.substring(0, c.indexOf('>'));
            } else if(c.indexOf('<') > -1) {
                if(c.indexOf('=') > -1) {
                    String versionNumber = c.substring(c.indexOf('=') + 1);
                    versionPredicate = (Package p) -> p.getVersion().compareTo(versionNumber) <= 0;
                } else {
                    String versionNumber = c.substring(c.indexOf('<') + 1);
                    versionPredicate = (Package p) -> p.getVersion().compareTo(versionNumber) < 0;
                }
                packageName = c.substring(0, c.indexOf('<'));
            } else if(c.indexOf('=') > -1) {
                String versionNumber = c.substring(c.indexOf('=') + 1);
                versionPredicate = (Package p) -> p.getVersion().equals(versionNumber);
                packageName = c.substring(0, c.indexOf('='));
            } else {
                versionPredicate = (Package p) -> true;
                packageName = c;
            }

            Set<Package> matchingPackages = Optional.ofNullable(packageVersions.get(packageName)).orElse(new HashSet<>()).stream().filter(versionPredicate).collect(Collectors.toSet());
            resultPackages.add(matchingPackages);
        }

        return resultPackages;
    }

    private static String stripVersionNumber(String versionNumber) {
        String[] parts = versionNumber.split(".");
        StringBuffer result = new StringBuffer();
        for(String nextPart : parts) {
            Integer nextPartInt = Integer.parseInt(nextPart);
            result.append(nextPartInt + ".");
        }

        if(result.indexOf(".") != -1) result.deleteCharAt(result.length() - 1);

        return result.toString();
    }

    /**
     * Extracts a set of packages from a string of package dependencies or conflicts, throws an exception if a package has dependencies that don't exist in the repository
     * @param packageString
     * @param packageVersions
     * @return
     */
    private static Set<Set<Package>> getPackagesFromStringWithException(List<String> packageString, Map<String, Set<Package>> packageVersions) throws NonexistantDependencyException {
        Set<Set<Package>> resultPackages = new HashSet<>();

        for(String c : packageString) {
            String packageName = "";

            Predicate<Package> versionPredicate;
            if(c.indexOf('>') > -1) {
                if(c.indexOf('=') > -1) {
                    String versionNumber = c.substring(c.indexOf('=') + 1);
                    versionPredicate = (Package p) -> p.getVersion().compareTo(versionNumber) >= 0;
                } else {
                    String versionNumber = c.substring(c.indexOf('>') + 1);
                    versionPredicate = (Package p) -> p.getVersion().compareTo(versionNumber) > 0;
                }
                packageName = c.substring(0, c.indexOf('>'));
            } else if(c.indexOf('<') > -1) {
                if(c.indexOf('=') > -1) {
                    String versionNumber = c.substring(c.indexOf('=') + 1);
                    versionPredicate = (Package p) -> p.getVersion().compareTo(versionNumber) <= 0;
                } else {
                    String versionNumber = c.substring(c.indexOf('<') + 1);
                    versionPredicate = (Package p) -> p.getVersion().compareTo(versionNumber) < 0;
                }
                packageName = c.substring(0, c.indexOf('<'));
            } else if(c.indexOf('=') > -1) {
                String versionNumber = c.substring(c.indexOf('=') + 1);
                versionPredicate = (Package p) -> p.getVersion().equals(versionNumber);
                packageName = c.substring(0, c.indexOf('='));
            } else {
                versionPredicate = (Package p) -> true;
                packageName = c;
            }

            if(packageVersions.get(packageName) != null && !packageVersions.get(packageName).isEmpty()) {
                Set<Package> matchingPackages = packageVersions.get(packageName).stream().filter(versionPredicate).collect(Collectors.toSet());

                if(!matchingPackages.isEmpty())
                    resultPackages.add(matchingPackages);
            }
        }
        if(resultPackages.isEmpty() && !packageString.isEmpty()) throw new NonexistantDependencyException();
        return resultPackages;
    }

    private static Formula negateAllAndGenerateAnd(Set<Package> packages, FormulaFactory f) {
        List<Formula> negatedPackages = packages.stream().map(nextPackage -> f.not(getPackageVariable(nextPackage, f))).collect(Collectors.toList());
        return f.and(negatedPackages);
    }

    private static Formula generatePackageDefinitionsFormula(List<Package> repo, FormulaFactory f, Map<String, Set<Package>> packageVersions) {
        List<Formula> packageDefinitionFormulas = new LinkedList<>();

        for(Package nextRepoPackage : repo) {
            try {
                Formula packageDefinitionFormula = f.not(getPackageVariable(nextRepoPackage, f));
                Formula packageDependenciesFormula = getPackageDependenciesFormula(nextRepoPackage, f, packageVersions);
                Formula packageConflictsFormula = getPackageConflictsFormula(nextRepoPackage, f, packageVersions);
                packageDefinitionFormulas.add(f.or(packageDefinitionFormula, f.and(packageDependenciesFormula, packageConflictsFormula)));
            } catch(NonexistantDependencyException e) {
                packageDefinitionFormulas.add(f.not(getPackageVariable(nextRepoPackage, f)));
            }


        }

        return f.and(packageDefinitionFormulas);
    }

  static String readFile(String filename) throws IOException {
    BufferedReader br = new BufferedReader(new FileReader(filename));
    StringBuilder sb = new StringBuilder();
    br.lines().forEach(line -> sb.append(line));
    return sb.toString();
  }

  static void printAnswer(List<Package> repo) {

    // CHANGE CODE BELOW:
    // using repo, initial and constraints, compute a solution and print the answer
    for (Package p : repo) {
      System.out.printf("package %s version %s\n", p.getName(), p.getVersion());
      for (List<String> clause : p.getDepends()) {
        System.out.printf("  dep:");
        for (String q : clause) {
          System.out.printf(" %s", q);
        }
        System.out.printf("\n");
      }
    }
  }
}
