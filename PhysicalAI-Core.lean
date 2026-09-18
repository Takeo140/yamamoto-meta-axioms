License Apache 2.0  Takeo Yamamoto
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Basic

namespace FTheory

/-!
  Physical AI Computational Core

  Sensor
    ↓
  Physical State
    ↓
  World Model
    ↓
  Safety Constraint
    ↓
  Controller
    ↓
  Action
    ↓
  State Transition
    ↓
  Sensor

  Fail-closed:
    invalid / unsafe state → Halt
-/

/- ============================================================
   Basic physical quantities
   ============================================================ -/

structure Vec3 where
  x : ℝ
  y : ℝ
  z : ℝ
  deriving Repr

def Vec3.zero : Vec3 :=
  { x := 0, y := 0, z := 0 }

def Vec3.add (a b : Vec3) : Vec3 :=
  { x := a.x + b.x
    y := a.y + b.y
    z := a.z + b.z }

def Vec3.sub (a b : Vec3) : Vec3 :=
  { x := a.x - b.x
    y := a.y - b.y
    z := a.z - b.z }

def Vec3.scale (a : ℝ) (v : Vec3) : Vec3 :=
  { x := a * v.x
    y := a * v.y
    z := a * v.z }

/- ============================================================
   Physical state
   ============================================================ -/

/-- Physical state observed by the AI. -/
structure PhysicalState where
  position : Vec3
  velocity : Vec3
  acceleration : Vec3
  mass : ℝ
  time : ℝ
  valid : Prop
  deriving Repr

/-- Force applied to the physical system. -/
structure Force where
  value : Vec3
  maxMagnitude : ℝ
  deriving Repr

/-- Actuator command. -/
structure Action where
  force : Force
  emergencyStop : Bool
  deriving Repr

/- ============================================================
   Sensor layer
   ============================================================ -/

/-- Sensor measurement. -/
structure SensorData where
  state : PhysicalState
  confidence : ℝ
  valid : Bool
  deriving Repr

/-- Sensor validity condition. -/
def SensorSafe (s : SensorData) : Prop :=
  s.valid = true ∧
  s.confidence ≥ 0.0 ∧
  s.confidence ≤ 1.0

/- ============================================================
   World model
   ============================================================ -/

/--
  World model.

  This is deliberately separated from raw sensor data.
-/
structure WorldModel where
  state : PhysicalState
  predicted : PhysicalState
  uncertainty : ℝ
  deriving Repr

/-- Construct a world model from sensor observations. -/
def buildWorldModel
    (s : SensorData)
    (predicted : PhysicalState)
    (h : SensorSafe s) :
    WorldModel :=
  { state := s.state
    predicted := predicted
    uncertainty := 1.0 - s.confidence }

/- ============================================================
   Safety layer
   ============================================================ -/

/-- Physical safety limits. -/
structure SafetyLimits where
  maxVelocity : ℝ
  maxAcceleration : ℝ
  maxForce : ℝ
  minMass : ℝ
  deriving Repr

/-- Basic physical safety condition. -/
def PhysicallySafe
    (s : PhysicalState)
    (limits : SafetyLimits) : Prop :=
  s.mass ≥ limits.minMass ∧
  s.velocity.x ≤ limits.maxVelocity ∧
  s.velocity.y ≤ limits.maxVelocity ∧
  s.velocity.z ≤ limits.maxVelocity ∧
  s.acceleration.x ≤ limits.maxAcceleration ∧
  s.acceleration.y ≤ limits.maxAcceleration ∧
  s.acceleration.z ≤ limits.maxAcceleration

/-- Safe action condition. -/
def ActionSafe
    (a : Action)
    (limits : SafetyLimits) : Prop :=
  a.force.maxMagnitude ≤ limits.maxForce

/- ============================================================
   Control objective
   ============================================================ -/

/-- Target physical state. -/
structure Target where
  position : Vec3
  velocity : Vec3
  deriving Repr

/-- Control error. -/
structure ControlError where
  positionError : Vec3
  velocityError : Vec3
  deriving Repr

def computeError
    (state : PhysicalState)
    (target : Target) :
    ControlError :=
  { positionError :=
      target.position.sub state.position

    velocityError :=
      target.velocity.sub state.velocity }

/- ============================================================
   Controller
   ============================================================ -/

/--
  Proportional controller.

  This is intentionally simple:
  the computational core can later be replaced by
  MPC / optimal control / learned policy.
-/
def controller
    (state : PhysicalState)
    (target : Target)
    (kp kv : ℝ)
    (maxForce : ℝ) :
    Action :=

  let e := computeError state target

  let raw :=
    e.positionError.scale kp
      |>.add (e.velocityError.scale kv)

  { force :=
      { value := raw
        maxMagnitude := maxForce }

    emergencyStop := false }

/- ============================================================
   Fail-closed decision layer
   ============================================================ -/

/-- Controller decision. -/
inductive Decision
  | Execute (action : Action)
  | Halt (reason : String)
  deriving Repr

/--
  Fail-closed safety gate.

  Missing/invalid sensor data or unsafe physical state
  causes HALT rather than execution.
-/
def safetyGate
    (sensor : SensorData)
    (world : WorldModel)
    (action : Action)
    (limits : SafetyLimits) :
    Decision :=

  if sensor.valid = false then
    Decision.Halt "SENSOR_FAILURE"

  else if sensor.confidence < 0.5 then
    Decision.Halt "LOW_CONFIDENCE"

  else if ¬ PhysicallySafe world.state limits then
    Decision.Halt "PHYSICAL_STATE_UNSAFE"

  else if ¬ ActionSafe action limits then
    Decision.Halt "ACTION_LIMIT_EXCEEDED"

  else
    Decision.Execute action

/- ============================================================
   Physical state transition
   ============================================================ -/

/--
  Discrete Newtonian transition.

  v(t+dt) = v(t) + a*dt
  x(t+dt) = x(t) + v*dt
-/
def integrate
    (state : PhysicalState)
    (force : Force)
    (dt : ℝ) :
    PhysicalState :=

  let acceleration :=
    force.value.scale (1.0 / state.mass)

  let velocity :=
    state.velocity.add
      (acceleration.scale dt)

  let position :=
    state.position.add
      (velocity.scale dt)

  { state with
      position := position
      velocity := velocity
      acceleration := acceleration
      time := state.time + dt }

/- ============================================================
   Execute one physical AI step
   ============================================================ -/

/--
  One complete perception → decision → action cycle.
-/
def step
    (sensor : SensorData)
    (world : WorldModel)
    (target : Target)
    (limits : SafetyLimits)
    (kp kv dt : ℝ) :
    Decision × WorldModel :=

  let action :=
    controller
      world.state
      target
      kp
      kv
      limits.maxForce

  match safetyGate sensor world action limits with

  | Decision.Halt reason =>
      (Decision.Halt reason, world)

  | Decision.Execute a =>
      let nextState :=
        integrate
          world.state
          a.force
          dt

      let nextWorld :=
        { world with
            state := nextState }

      (Decision.Execute a, nextWorld)

/- ============================================================
   Repeated physical simulation
   ============================================================ -/

/-- Execute a finite control sequence. -/
def simulate
    (steps : Nat)
    (sensor : SensorData)
    (world : WorldModel)
    (target : Target)
    (limits : SafetyLimits)
    (kp kv dt : ℝ) :
    WorldModel :=

  match steps with

  | 0 =>
      world

  | n + 1 =>
      let (_, nextWorld) :=
        step
          sensor
          world
          target
          limits
          kp
          kv
          dt

      simulate
        n
        sensor
        nextWorld
        target
        limits
        kp
        kv
        dt

/- ============================================================
   Formal safety properties
   ============================================================ -/

/--
  If sensor validity fails, the safety gate cannot execute
  the action.
-/
theorem sensor_failure_halts
    (sensor : SensorData)
    (world : WorldModel)
    (action : Action)
    (limits : SafetyLimits)
    (h : sensor.valid = false) :
    safetyGate sensor world action limits
      = Decision.Halt "SENSOR_FAILURE" := by
  simp [safetyGate, h]

/--
  If confidence is below the required threshold,
  execution is prevented.
-/
theorem low_confidence_halts
    (sensor : SensorData)
    (world : WorldModel)
    (action : Action)
    (limits : SafetyLimits)
    (h : sensor.valid = true)
    (hc : sensor.confidence < 0.5) :
    safetyGate sensor world action limits
      = Decision.Halt "LOW_CONFIDENCE" := by
  simp [safetyGate, h, hc]

end FTheory
