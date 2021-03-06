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

class CircularDependencyException extends Exception {
    Set<Package> circularPackages;

    public CircularDependencyException(Set<Package> circularPackages) {
        super();
        this.circularPackages = circularPackages;
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
    private static Set<Package> packagesWeCareAbout = new HashSet<>();
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
          String versionNumber = c.substring(c.indexOf('=') + 1);
          versionPredicate = (Package p) -> comparePackageVersions(versionNumber, p.getVersion()) >= 0;
        } else {
          String versionNumber = c.substring(c.indexOf('>') + 1);
          versionPredicate = (Package p) -> comparePackageVersions(versionNumber, p.getVersion()) > 0;
        }
        packageName = c.substring(1, c.indexOf('>'));
      } else if(c.indexOf('<') > -1) {
        if(c.indexOf('=') > -1) {
          String versionNumber = c.substring(c.indexOf('=') + 1);
          versionPredicate = (Package p) -> comparePackageVersions(versionNumber, p.getVersion()) <= 0;
        } else {
          String versionNumber = c.substring(c.indexOf('>') + 1);
          versionPredicate = (Package p) -> comparePackageVersions(versionNumber, p.getVersion()) < 0;
        }
        packageName = c.substring(1, c.indexOf('<'));
      } else if(c.indexOf('=') > -1) {
        String versionNumber = c.substring(c.indexOf('=') + 1);
        versionPredicate = (Package p) -> comparePackageVersions(versionNumber, p.getVersion()) == 0;
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

    Set<Package> lowestScoreInstallsWithCircular = null;
    Set<Package> lowestScoreDoNotInstallsWithCircular = null;
    Set<Package> lowestScoreCirculars = null;

    Long lowestScore = Long.MAX_VALUE;

    for(Assignment nextModel : validModels) {
        Set<Package> install = nextModel.positiveLiterals().stream().map(v -> stringToPackageMappings.get(v.name())).collect(Collectors.toSet());
        Set<Package> doNotInstall = nextModel.negativeVariables().stream().map(v -> stringToPackageMappings.get(v.name())).collect(Collectors.toSet());

        Long score = calculateModelScore(install, doNotInstall, initialPackages);

        if(score <= lowestScore) {
            try {
                lowestScoreInstalls = getOrderOfInstallsFast(install, doNotInstall, packageVersions);
                lowestScoreDoNotInstalls = doNotInstall;
                lowestScore = score;
            } catch(CircularDependencyException e) {
                lowestScoreDoNotInstallsWithCircular = doNotInstall;
                lowestScoreCirculars = e.circularPackages;
                lowestScoreInstallsWithCircular = getSetDifference(install, lowestScoreCirculars);
            }
        }
    }

    if(validModels.isEmpty() || lowestScoreInstalls == null) {
        if(lowestScoreCirculars != null) {
            tryResolveCircular(initialPackages, lowestScoreInstallsWithCircular, lowestScoreDoNotInstallsWithCircular, lowestScoreCirculars, packageVersions);
            return;
        } else {
            System.out.println("[]");
            return;
        }
    }


    Set<Package> uninstalls = getSetIntersection(lowestScoreDoNotInstalls, initialPackages);
    initialPackages.removeAll(uninstalls);

//    LinkedList<Package> installs = getOrderOfInstallsSlow(initialPackages, lowestScoreInstalls, packageVersions);

    System.out.print('[');
    String actionString = "";
    for(Package nextUninstall : uninstalls) {
        actionString += constructStringForInstall(nextUninstall, false) + ',';
    }

    for(Package nextInstall : lowestScoreInstalls) {
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

    /**
     * This currently only works under very limited circumstances - initial is empty, package required to break circle doesn't conflict with any existing ones, and there's only two circular guys
     * @param initial
     * @param install
     * @param circulars
     * @param packageVersions
     */
  private static void tryResolveCircular(Set<Package> initial, Set<Package> install, Set<Package> doNotInstall, Set<Package> circulars, Map<String, Set<Package>> packageVersions) {
      if(circulars.size() != 2) {
          System.out.println("[]");
          return;
      }

      LinkedList<String> result = new LinkedList<>();

      LinkedList<Package> installedPackages = new LinkedList<>();

      LinkedList<Package> packageQueue = new LinkedList<>(install);

      while(!packageQueue.isEmpty()) {
          Package p = packageQueue.pollFirst();

          if(hasUnmetDependencies(p, installedPackages, packageVersions)) {
              packageQueue.addLast(p);
          } else {
              installedPackages.add(p);
              result.add(constructStringForInstall(p, true));
          }
      }

      List<Package> circularsAsList = new ArrayList<>(circulars);

      Package circular1 = circularsAsList.get(0);
      Package circular2 = circularsAsList.get(1);

      List<List<String>> circular1DependenciesRaw = circular1.getDepends();

      for(List<String> nextCircular1DependencyRaw : circular1DependenciesRaw) {
          Set<Set<Package>> nextCircular1Dependency = getPackagesFromString(nextCircular1DependencyRaw, packageVersions);
          boolean dependencyMet = false;

          for(Set<Package> nextCircular1DependencyOuter : nextCircular1Dependency) {
              for(Package nextCircular1DependencyInner : nextCircular1DependencyOuter) {
                  if(installedPackages.contains(nextCircular1DependencyInner)) {
                      dependencyMet = true;
                      break;
                  }

                  if(dependencyMet) break;
              }
          }

          if(!dependencyMet) {
              for(Set<Package> nextUnmetDependencyOuter : nextCircular1Dependency) {
                  for(Package nextUnmetDependencyInner : nextUnmetDependencyOuter) {
                      if(nextUnmetDependencyInner != circular2) {
                          Set<Package> previouslyInstalledConflicts = new HashSet<>();

                          for(Package p : installedPackages) {
                              List<String> conflictsRaw = p.getConflicts();
                              Set<Set<Package>> conflicts = getPackagesFromString(conflictsRaw, packageVersions);

                              for(Set<Package> nextConflictOuter : conflicts) {
                                  for(Package nextConflictInner : nextConflictOuter) {
                                      if(nextConflictInner == nextUnmetDependencyInner) {
                                          previouslyInstalledConflicts.add(p);
                                      }
                                  }
                              }
                          }

                          for(Package nextPreviouslyInstalledConflict : previouslyInstalledConflicts) {
                              result.add(constructStringForInstall(nextPreviouslyInstalledConflict, false));
                          }
                          result.add(constructStringForInstall(nextUnmetDependencyInner, true));
                          result.add(constructStringForInstall(circular1, true));
                          result.add(constructStringForInstall(circular2, true));
                          result.add(constructStringForInstall(nextUnmetDependencyInner, false));

                          for(Package nextPreviouslyInstalledConflict : previouslyInstalledConflicts) {
                              result.add(constructStringForInstall(nextPreviouslyInstalledConflict, true));
                          }


                          System.out.print('[');
                          String commandString = "";
                          for(String nextCommand : result) {
                              commandString += nextCommand + ',';
                          }
                          if(commandString.indexOf(',') != -1) commandString = commandString.substring(0, commandString.length() - 1);
                          System.out.print(commandString);
                          System.out.print(']');
                          return;
                      }
                  }
              }
          }
      }

      System.out.println("[]");
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

  private static LinkedHashSet<Package> getOrderOfInstallsFast(Set<Package> install, Set<Package> doNotInstall, Map<String, Set<Package>> packageVersions) throws CircularDependencyException {
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

                    if(!validDependenciesOrInner.isEmpty()) validDependenciesOrOuter.add(validDependenciesOrInner.getFirst()); // we only care about one that matches. we can stop as soon as we find one
                }

                validDependenciesAnd.add(validDependenciesOrOuter.getFirst());
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

      if(result.size() < install.size()) {
          Set<Package> difference = new HashSet<>(install);
          difference.removeAll(result);
          throw new CircularDependencyException(difference);
      }
      Collections.reverse(result); // need to avoid creating a circular guy, as happens in seen-6
      return new LinkedHashSet<>(result);
  }

  private static int comparePackageVersions(String a, String b) {
      if(a.equals(b)) return 0;
      
      String[] aSplit = a.split("\\.");
      String[] bSplit = b.split("\\.");
      
      int minLength = Math.min(aSplit.length, bSplit.length);
      
      for(int i = 0; i <= minLength; i ++) {
          if(i == aSplit.length && i == bSplit.length) {
              return 0;
          } else if(i == aSplit.length && i < bSplit.length) {
              return 1;
          } else if(i == bSplit.length && i < aSplit.length) {
              return -1;
          }
          
          String aPart = aSplit[i];
          String bPart = bSplit[i];
          
          int aInt = Integer.parseInt(aPart);
          int bInt = Integer.parseInt(bPart);
          
          if(aInt > bInt) return -1;
          else if(aInt < bInt) return 1;
      }
      
      return 0;
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
          if(!initial.contains(installed)) score += (long)(installed.getSize());
      }

      score += 1000000L * (getSetIntersection(doNotInstall, initial).size());

      return score;
  }

  private static Set<Package> getSetIntersection(Set<Package> set1, Set<Package> set2) {
      Set<Package> doNotInstallAndInitialIntersection = new HashSet<>(set1);
      doNotInstallAndInitialIntersection.retainAll(set2);

      return doNotInstallAndInitialIntersection;
  }

    private static Set<Package> getSetDifference(Set<Package> set1, Set<Package> set2) {
        Set<Package> doNotInstallAndInitialIntersection = new HashSet<>(set1);
        doNotInstallAndInitialIntersection.removeAll(set2);

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

    Set<Package> packagesWeCareAbout = new HashSet<>();
    Set<Package> alreadyExpanded = new HashSet<>();

    for(Set<Package> nextMustInstallAndGroup : packages) {
        List<Formula> mustInstallOrFormulas = new LinkedList<>();

        for(Package nextMustInstallOr : nextMustInstallAndGroup) {
            mustInstallOrFormulas.add(getPackageVariable(nextMustInstallOr, f));
            getPackagesWeCareAbout(nextMustInstallOr, packagesWeCareAbout, alreadyExpanded, packageVersions);
        }

        Formula mustInstallOrFormula = f.or(mustInstallOrFormulas);
        mustInstallAndFormulas.add(mustInstallOrFormula);
    }

    packagesWeCareAbout.addAll(doNotWantPackages);

    Formula mustInstallAndFormula = f.and(mustInstallAndFormulas);

    Formula finalFormula = f.and(packageDefinitionsFormula, mustNotInstall, mustInstallAndFormula);
      final SATSolver miniSat = MiniSat.miniSat(f);
    miniSat.add(finalFormula);
    miniSat.sat();




    Set<Variable> variablesWeCareAbout = packagesWeCareAbout.stream().map(p -> getPackageVariable(p, f)).collect(Collectors.toSet());
//    List<Assignment> possibleModels = Collections.singletonList(miniSat.model(variablesWeCareAbout));
    List<Assignment> possibleModels = miniSat.enumerateAllModels(variablesWeCareAbout); // get OutOfMemoryError here. use a list of variables that's filtered on ones we're definitely not using?
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

  private static Set<Package> getPackagesWeCareAbout(Package p, Set<Package> answer, Set<Package> alreadyExpanded, Map<String, Set<Package>> packageVersions) {
      if(alreadyExpanded.contains(p)) return answer;
      alreadyExpanded.add(p);
      answer.add(p);

      List<String> packageConflictsRaw = p.getConflicts();
      Set<Set<Package>> packageConflicts = getPackagesFromString(packageConflictsRaw, packageVersions);

      for(Set<Package> nextPackageConflictOuter : packageConflicts) {
          for(Package nextPackageConflictInner : nextPackageConflictOuter) {
              answer.add(nextPackageConflictInner);
          }
      }

      List<List<String>> packageDependenciesRaw = p.getDepends();
      for(List<String> nextPackageDependencyRaw : packageDependenciesRaw) {
          Set<Set<Package>> nextPackageDependency = getPackagesFromString(nextPackageDependencyRaw, packageVersions);
          for(Set<Package> nextPackageDependencyOuter : nextPackageDependency) {
              for(Package nextPackageDependencyInner : nextPackageDependencyOuter) {
                  getPackagesWeCareAbout(nextPackageDependencyInner, answer, alreadyExpanded, packageVersions);
              }
          }
      }

      return answer;
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
                    versionPredicate = (Package p) -> comparePackageVersions(versionNumber, p.getVersion()) >= 0;
                } else {
                    String versionNumber = c.substring(c.indexOf('>') + 1);
                    versionPredicate = (Package p) -> comparePackageVersions(versionNumber, p.getVersion()) > 0;
                }
                packageName = c.substring(0, c.indexOf('>'));
            } else if(c.indexOf('<') > -1) {
                if(c.indexOf('=') > -1) {
                    String versionNumber = c.substring(c.indexOf('=') + 1);
                    versionPredicate = (Package p) -> comparePackageVersions(versionNumber, p.getVersion()) <= 0;
                } else {
                    String versionNumber = c.substring(c.indexOf('<') + 1);
                    versionPredicate = (Package p) -> comparePackageVersions(versionNumber, p.getVersion()) < 0;
                }
                packageName = c.substring(0, c.indexOf('<'));
            } else if(c.indexOf('=') > -1) {
                String versionNumber = c.substring(c.indexOf('=') + 1);
                versionPredicate = (Package p) -> comparePackageVersions(versionNumber, p.getVersion()) == 0;
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
                    versionPredicate = (Package p) -> comparePackageVersions(versionNumber, p.getVersion()) >= 0;
                } else {
                    String versionNumber = c.substring(c.indexOf('>') + 1);
                    versionPredicate = (Package p) -> comparePackageVersions(versionNumber, p.getVersion()) > 0;
                }
                packageName = c.substring(0, c.indexOf('>'));
            } else if(c.indexOf('<') > -1) {
                if(c.indexOf('=') > -1) {
                    String versionNumber = c.substring(c.indexOf('=') + 1);
                    versionPredicate = (Package p) -> comparePackageVersions(versionNumber, p.getVersion()) <= 0;
                } else {
                    String versionNumber = c.substring(c.indexOf('<') + 1);
                    versionPredicate = (Package p) -> comparePackageVersions(versionNumber, p.getVersion()) < 0;
                }
                packageName = c.substring(0, c.indexOf('<'));
            } else if(c.indexOf('=') > -1) {
                String versionNumber = c.substring(c.indexOf('=') + 1);
                versionPredicate = (Package p) -> comparePackageVersions(versionNumber, p.getVersion()) == 0;
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
}
