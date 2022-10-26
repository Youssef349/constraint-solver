package constraintLibrary

case class Domain[A](values: Set[A]):
  def union(domain: Domain[A]): Domain[A] = Domain(values.union(domain.values))
  def union(value: A): Domain[A] = union(domain = Domain[A](Set(value)))
  def intersect(domain: Domain[A]): Domain[A] = Domain(values.intersect(domain.values))
  def intersect(value: A): Domain[A] = intersect(domain = Domain[A](Set(value)))
  def diff(domain: Domain[A]): Domain[A] = Domain(values.diff(domain.values))
  def diff(value: A): Domain[A] = diff(domain = Domain[A](Set(value)))
  def isEmpty: Boolean = values.isEmpty
  def isSingleton: Boolean = values.size == 1
  def toSingleton: Domain[A] = Domain(Set(values.head))

case class Variable[A](name: String)

enum Constraint[A]:
  case EqualVariables(x: Variable[A], y: Variable[A])
  case EqualConstant(x: Variable[A], c: A)
  case DiffVariables(x: Variable[A], y: Variable[A])
  case DiffConstant(x: Variable[A], c: A)
  case AllDiff(variables: List[Variable[A]])

case class CSP[A](domains: Map[Variable[A], Domain[A]], constraints: List[Constraint[A]]):
  object cacheAllDiff { // No need to do setAllDomainsDiff again
    var cache: List[Domain[A]] = null
  }

  def solve: Map[Variable[A], Domain[A]] =
    val constraint: Option[Constraint[A]] = constraints.find(c => !Achieved(c))
    // find the first constraint not achieved

    constraint match
      //  all the constraint are achieved
      case None =>
        val varToReduce = domains.find(!_._2.isSingleton)
        varToReduce match
          case Some(v) =>
            //  the domain is empty so we can't solve the constraint
            if v._2.isEmpty then Map()
            // with the domains to reduce we fix a value and we resolve
            else
              val newCSP = Domainupdate(Map(v._1 -> v._2.toSingleton), constraints)
              newCSP.solve
          case None => domains
      case Some(x) => // not achieved constraint is found
        // We create a new CSP and resolve it  (recursively)
        val newMap = useConstraint(x)
        if (newMap.forall(_._2.isSingleton)) //resolved constraint : We take it away
          val newConstraints = constraints.diff(List(x))
          val newCSP = Domainupdate(newMap, newConstraints)
          newCSP.solve
        else
          val newCSP = Domainupdate(newMap, constraints)
          newCSP.solve

  def Achieved(constraint: Constraint[A]): Boolean =
  // Verify achieved or not
    constraint match
      case Constraint.EqualVariables(x, y) =>
        areDomainsSame(domains(x), domains(y))

      case Constraint.EqualConstant(x, c) =>
        areDomainsSame(domains(x), Domain(Set(c)))

      case Constraint.DiffVariables(x, y) =>
        areDomainsDiff(domains(x), domains(y))

      case Constraint.DiffConstant(x, c) =>
        areDomainsDiff(domains(x), Domain(Set(c)))

      case Constraint.AllDiff(variables) =>
        val oldDomains: List[Domain[A]] = variables.map(v => domains(v))
        val newDomains: List[Domain[A]] = setAllDomainsDiff(variables.map(v => domains(v)))
        if (newDomains == oldDomains) true // Achieved
        else
          cacheAllDiff.cache = newDomains //  not Achieved -> we stock newDomains
          false

      case _ => true

  def useConstraint(constraint: Constraint[A]): Map[Variable[A], Domain[A]] =
  // Apply the constraint to the variable concerned
  // Returns a Map which allows to update the "domains"
    constraint match
      case Constraint.EqualVariables(x, y) =>
        val newDomain: Domain[A] = sameDomains(domains(x), domains(y))
        Map(x -> newDomain, y -> newDomain)

      case Constraint.EqualConstant(x, c) =>
        Map(x -> sameDomains(domains(x), Domain(Set(c))))

      case Constraint.DiffVariables(x, y) =>
        val newDomain: List[Domain[A]] = differenceDomains(domains(x), domains(y))
        Map(x -> newDomain.head, y -> newDomain.last)

      case Constraint.DiffConstant(x, c) =>
        Map(x -> differenceConstantDomains(domains(x), Domain(Set(c))))

      case Constraint.AllDiff(variables: List[Variable[A]]) =>
        val newDomains = cacheAllDiff.cache
        variables.zip(newDomains).toMap

      case _ => Map() // Unknown constraint

  def Domainupdate(newDomains: Map[Variable[A], Domain[A]], newConstraints: List[Constraint[A]]): CSP[A] =
    copy(domains = domains ++ newDomains, constraints = newConstraints)
  // Create a new CSP object with the domains updated

  def areDomainsDiff(x: Domain[A], y: Domain[A]): Boolean =
    if (x.isSingleton || y.isSingleton) x.intersect(y).isEmpty
    else true

  def differenceDomains(x: Domain[A], y: Domain[A]): List[Domain[A]] =
    if (x.isSingleton) List(x, y.diff(x))

    else if (y.isSingleton) List(x.diff(y), y)

    else List(x, y)

  //Returns a list of domains x and y

  def sameDomains(x: Domain[A], y: Domain[A]): Domain[A] =
    x.intersect(y)
  // Returns the intersection of domains x and y

  def differenceConstantDomains(x: Domain[A], y: Domain[A]): Domain[A] =
    x.diff(y)

  def areDomainsSame(x: Domain[A], y: Domain[A]): Boolean =
    x.values.equals(y.values)
  // True if the domains are equal


  def mapDomainsMix(domainsList: List[List[A]]): List[List[A]] =
    domainsList match
      case Nil => List(Nil)
      case xs :: tail =>
        val combinationsTail = mapDomainsMix(tail)
        xs.flatMap(x =>
          combinationsTail.flatMap(c =>
            val nList = x::c
            if (nList.distinct.size == nList.size) Some(x::c)
            else None
          )
        )
        
  def setAllDomainsDiff(domainsList: List[Domain[A]]): List[Domain[A]] =
    val allCombinations = mapDomainsMix(domainsList.map(d => d.values.toList))
    allCombinations.transpose.map(l => Domain(l.toSet))
