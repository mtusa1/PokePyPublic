import random
import csv
import copy
import pickle
import glob
import requests
import subprocess
import shutil
import os
import pandas as pd
import numpy as np
import sys
import pygame
import pytmx
import math
import serial
import json
import smartcard
from smartcard.System import readers
from smartcard.util import toHexString
from pygame.locals import KEYDOWN, K_0, K_1, K_2, K_3, K_4, K_5, K_6
from pytmx.util_pygame import load_pygame
from functools import partial
from copy import deepcopy
from PIL import Image
from PIL import ImageSequence



class ExitBattle(Exception):
    pass
class PokemonCaptured(Exception):
    pass
class IncompatibleMoveType(Exception):
    pass

# Add Git executable path to sys.path
sys.path.append('https://github.com/mtusa1/PokePyMain.git')  # Replace '/path/to/git' with the actual path of the Git executable


frames_directory = "frames"
if not os.path.exists(frames_directory):
    os.makedirs(frames_directory)

font_path = "pixeled.ttf"
last_global_click = 0

# Global button positions
global human_buttons_x_pos, other_buttons_x_pos
human_buttons_x_pos = 0
other_buttons_x_pos = 0

# Global variable to store the scanned Pokémon data
scanned_pokemon_data = None


class Pokemon:
    id_counter = 0  # This is a class-level attribute that gets shared across all instances of the class
    critical_hit_ratio = 0.1  # This is a class-level attribute that gets shared across all instances of the class
    max_moves = 4

    def __init__(self, attributes):
        self.id = Pokemon.id_counter
        Pokemon.id_counter += 1  # Increment the counter each time a new instance is created

        # Data validation
        if not isinstance(attributes['Name'], str):
            raise TypeError("Name must be a string.")
        if not isinstance(attributes['Level'], int) or attributes['Level'] < 1:
            raise ValueError("Level must be a positive integer.")
        if not isinstance(attributes['Type'], list) or not all(isinstance(t, str) for t in attributes['Type']):  # Check if ptype is a list of strings
            raise TypeError("Type must be a list of strings.")
        if not isinstance(attributes['Max_Health'], int) or attributes['Max_Health'] < 0:
            raise ValueError("Max health must be a non-negative integer.")
        if not isinstance(attributes['Attack'], int) or attributes['Attack'] < 0:
            raise ValueError("Attack must be a non-negative integer.")
        if not isinstance(attributes['Defense'], int) or attributes['Defense'] < 0:
            raise ValueError("Defense must be a non-negative integer.")
        if not isinstance(attributes['Speed'], int) or attributes['Speed'] < 0:
            raise ValueError("Speed must be a non-negative integer.")
        if not all(isinstance(move, Move) for move in attributes['Moves']):
            raise TypeError("All elements in Moves must be instances of the Move class.")
        self.critical_hit_ratio = attributes.get('Critical_Hit_Ratio', 0.1)  # Use the value from attributes if it exists, otherwise use 0.1
        if not isinstance(self.critical_hit_ratio, (int, float)) or self.critical_hit_ratio < 0:
            raise ValueError("Critical hit ratio must be a non-negative number.")
        self.prevent_stat_lower_flag = attributes.get('Prevent_Stat_Lower', False)  # Use the value from attributes if it exists, otherwise use False
        if not isinstance(self.prevent_stat_lower_flag, bool):
            raise ValueError("Prevent stat lower must be a boolean.")
        # Now 'Region' must be a list of strings
        if not all(isinstance(region, str) for region in attributes['Region']):
            raise TypeError("All elements in Region must be strings.")

        self.name = attributes['Name']
        self.index = attributes['Index']
        self.level = attributes['Level']
        self.ptype = attributes['Type']  # this could be a list of types if a Pokemon has a secondary type
        self.max_health = attributes['Max_Health']
        self.current_health = attributes['Max_Health']
        self.attack = attributes['Attack']
        self.defense = attributes['Defense']
        self.speed = attributes['Speed']
        self.moves = attributes['Moves']
        self.moves_to_learn = attributes['Moves_to_Learn']
        self.last_moves_learned = []
        self.evolved_form = attributes['Evolved_Form']
        self.evolution_item = attributes['Evolution_Item']
        self.abilities = attributes['Abilities'] if attributes['Abilities'] else []
        self.held_item = attributes['Held_Item']
        self.experience = 0
        self.level_up_experience = self.level * 100  # or some other calculation
        self.status = 'normal'
        self.status_effect = None
        self.sleep_turns = None  # Add this line
        self.region = attributes['Region']
        self.sub_region = attributes['Sub_Region']
        self.mana_cost = attributes['Mana_Cost']
        self.rarity = attributes['Rarity']
        self.price = attributes['Price']
        self.description = attributes['Description']
        #self.critical_hit_ratio = attributes.get('Critical_Hit_Ratio', 0.1)
        #self.prevent_stat_lower = attributes.get('Prevent_Stat_Lower', False)


        if attributes['Evolution_Level'] is not None:
            try:
                self.evolution_level = int(attributes['Evolution_Level'])
            except ValueError:
                self.evolution_level = None
        else:
            self.evolution_level = None

        self.evolution_item = attributes['Evolution_Item']

    def __str__(self):
        info = [
            f"Name: {self.name}",
            f"Index: {self.index}",
            f"ID: {self.id}",  # Display the unique ID of the Pokemon
            f"Type: {self.ptype}",
            f"Health: {self.current_health}/{self.max_health}",
            f"Level: {self.level}",
            f"Attack: {self.attack}",
            f"Defense: {self.defense}",
            f"Speed: {self.speed}",
            f"Moves: {', '.join(str(move) for move in self.moves)}",

        ]

        if self.evolved_form:
            info.append(f"Evolved Form: {self.evolved_form}")
        if self.evolution_level:
            info.append(f"Evolution Level: {self.evolution_level}")
        if self.abilities:
            info.append(f"Abilities: {self.abilities}")
        if self.held_item:
            info.append(f"Held Item: {self.held_item}")

        info.extend([
            f"Experience: {self.experience}/{self.level_up_experience}",
            f"Status: {self.status}",
            f"Region: {self.region}",
            f"Sub Region: {self.sub_region}",
            f"Mana Cost: {self.mana_cost}",
            f"Rarity: {self.rarity}",
            f"Price: {self.price}",
            f"Description: {self.description}",
        ])

        if self.status_effect:
            info.append(f"Status Effect: {self.status_effect}")

        return "\n".join(info)

    def gain_experience(self, amount, moves_dict):
        """
        Increases the Pokemon's experience by the given amount.
        If the Pokemon has enough XP to level up, it levels up.
        """
        if self.current_health > 0:
            self.experience += amount
            print(f"{self.name} gained {amount} experience points!")
            print(f"{self.name}'s current experience: {self.experience}/{self.level_up_experience}")
            
            while self.experience >= self.level_up_experience:
                self.level_up(moves_dict)

    def level_up(self, moves_dict):
        """
        Increases the Pokemon's level by one and increases its stats.
        """
        self.level += 1
        self.experience -= self.level_up_experience
        self.level_up_experience = self.level * 100  # or some other calculation
        self.max_health += 10  # or some other calculation
        self.attack += 5  # or some other calculation
        self.defense += 5  # or some other calculation

        for move_name, level in self.moves_to_learn.items():
            if self.level == level:
                #print(f"level_up moves_dict: {moves_dict}")
                new_move = moves_dict[move_name]  # Get the Move object from moves_dict
                if len(self.moves) < 4:
                    # If the Pokemon knows less than 4 moves, it can simply learn the new move
                    self.moves.append(new_move)
                    print(f"{self.name} learned {new_move.name}!")
                else:
                    # If the Pokemon already knows 4 moves, prompt the user to choose a move to forget
                    print(f"{self.name} is trying to learn {new_move.name}, but it already knows 4 moves.")
                    print("Should a move be forgotten to make space for the new move?")
                    for i, move in enumerate(self.moves):
                        print(f"{i+1}. {move.name}")
                    move_to_forget = int(input("Enter the number of the move to forget, or 0 to give up on learning the new move: "))
                    if move_to_forget == 0:
                        print(f"{self.name} did not learn {new_move.name}.")
                    else:
                        forgotten_move = self.moves.pop(move_to_forget - 1)
                        self.moves.append(new_move)
                        print(f"{self.name} forgot {forgotten_move.name} and learned {new_move.name}!")

        if self.evolution_level is not None and self.level >= self.evolution_level:
            self.evolve()

        print(f"{self.name} leveled up to level {self.level}!")

    def evolve(self):
        if self.evolution_item is not None:
            self.evolve_with_item()
        elif self.level >= self.evolution_level:
            print(f"{self.name} is evolving!")
            self.name = self.evolved_form
            self.max_health += 20  # Increase stats upon evolution
            self.attack += 10
            self.defense += 10
            self.speed += 10
            print(f"{self.name} has evolved into {self.evolved_form}!")

    def evolve_with_item(self, item_name=None):
        print(f"Item name: {item_name}, Pokemon's evolution item: {self.evolution_item}")
        if item_name.lower() == self.evolution_item.lower():  # Compare in lowercase
            print(f"{self.name} is evolving!")
            self.name = self.evolved_form
            self.max_health += 20  # Increase stats upon evolution
            self.attack += 10
            self.defense += 10
            self.speed += 10
            print(f"{self.name} has evolved into {self.evolved_form}!")
            return True
        else:
            print(f"{self.name} can't evolve with {item_name}.")
            return False

    def take_damage(self, damage, cause=None):
        self.current_health -= damage
        print(f"Reduced current_health for {self.name} to {self.current_health} after taking damage")
        if self.current_health < 0:
            self.current_health = 0
        if cause:
            print(f"{self.name} took {damage} damage from {cause}!")
        else:
            print(f"{self.name} took {damage} damage!")

    def heal(self, amount):
        """
        Heal the Pokemon by a specified amount.

        Parameters:
        amount (int): The amount to heal the Pokemon by.

        Returns:
        None
        """
        print(f"Called heal with amount: {amount}")
        self.current_health += amount
        print(f"Increased current_health for {self.name} to {self.current_health} after healing")
        if self.current_health > self.max_health:
            self.current_health = self.max_health
        #print(f"{self.name} has been healed by {amount} points!")

    def revive(self):
        if self.current_health == 0:  # if the Pokemon is fainted
            self.current_health = self.max_health // 2  # revive it to half of its max health
            print(f"Revived {self.name} with current_health set to {self.current_health}")
            self.status = None
            print(f'{self.name} has been revived!')
            return True
        else:
            print(f'{self.name} is not fainted and can\'t be revived.')
            return False

    def modify_stat(self, stat, amount):
        """
        Modifies the given stat by the given amount.
        If the stat is a target stat, the target's stat is decreased.
        If the stat is not a target stat, the Pokemon's stat is increased.
        """
        if self.prevent_stat_lower_flag and amount < 0:
            print(f"{self.name}'s stats can't be lowered!")
            return

        current_value = getattr(self, stat)
        setattr(self, stat, current_value + amount)
        if amount > 0:
            print(f"{self.name}'s {stat} increased by {amount}!")
        else:
            print(f"{self.name}'s {stat} decreased by {-amount}!")

    def paralyze(self):
        self.status = 'paralyzed'
        print(f"{self.name} is paralyzed!")
        # Maybe a paralyzed Pokemon has a 25% chance to not be able to move each turn
        # Now the lambda function will return True when the Pokemon can't move and False when it can
        self.status_effect = lambda: random.choices([True, False], weights=[25, 75], k=1)[0]

    def freeze(self):
        self.status = 'frozen'
        print(f"{self.name} is frozen solid!")
        # Maybe a frozen Pokemon can't move until the status is cured
        self.status_effect = lambda: True

    def burn(self):
        self.status = 'burned'
        print(f"{self.name} is burned!")
        # Maybe a burned Pokemon loses 10% of its max health each turn
        self.status_effect = lambda: self.take_damage(int(self.max_health*0.1), 'burn')

    def poison(self):
        self.status = 'poisoned'
        print(f"{self.name} is poisoned!")
        # Maybe a poisoned Pokemon loses 15% of its max health each turn
        self.status_effect = lambda: self.take_damage(int(self.max_health*0.15), 'poison')

    def sleep(self):
        self.status = 'sleeping'
        print(f"{self.name} is asleep!")
        # Maybe a sleeping Pokemon can't move for 1-3 turns
        self.sleep_turns = random.randint(1, 3)
        self.status_effect = lambda: self.sleep_turns > 0

    def cure_poison(self):
        if self.status == 'poisoned':
            self.status = 'normal'
            self.status_effect = None
            print(f"{self.name} is no longer poisoned!")
            return True
        else:
            print(f"{self.name} is not poisoned.")
            return False

    def cure_sleep(self):
        if self.status == 'sleeping':
            self.status = 'normal'
            self.status_effect = None
            print(f"{self.name} has woken up!")
            return True
        else:
            print(f"{self.name} is not asleep.")
            return False

    def cure_paralysis(self):
        if self.status == 'paralyzed':
            self.status = 'normal'
            self.status_effect = None
            print(f"{self.name} is no longer paralyzed!")
            return True
        else:
            print(f"{self.name} is not paralyzed.")
            return False

    def cure_burn(self):
        if self.status == 'burned':
            self.status = 'normal'
            self.status_effect = None
            print(f"{self.name} is no longer burned!")
            return True
        else:
            print(f"{self.name} is not burned.")
            return False

    def cure_status(self):
        self.status = 'normal'
        self.status_effect = None
        print(f"{self.name} is cured of all status conditions!")
        return True

    def increase_max_health(self, amount):
        self.max_health += amount
        print(f"{self.name}'s max health increased by {amount}!")
        return True

    def increase_accuracy(self, amount):
        for move in self.moves:
            move.accuracy = min(100, move.accuracy + amount)
        print(f"{self.name}'s accuracy increased by {amount}!")
        return True

    def increase_attack(self, amount):
        self.attack += amount
        print(f"{self.name}'s attack increased by {amount}!")
        return True

    def increase_defense(self, amount):
        self.defense += amount
        print(f"{self.name}'s defense increased by {amount}!")
        return True

    def increase_speed(self, amount):
        self.speed += amount
        print(f"{self.name}'s speed increased by {amount}!")
        return True

    def increase_critical_hit_ratio(self, amount):
        # Assuming you have a critical_hit_ratio attribute in your Pokemon class
        self.critical_hit_ratio += amount
        print(f"{self.name}'s critical hit ratio increased by {amount}!")
        return True

    def prevent_stat_lower(self):
        # Assuming you have a prevent_stat_lower attribute in your Pokemon class
        self.prevent_stat_lower_flag = True
        print(f"{self.name}'s stats cannot be lowered!")
        return True

    def learn_move(self, move):
        # If the Pokemon already knows the maximum number of moves
        if len(self.moves) >= self.max_moves:
            print(f"{self.name} is trying to learn {move.name}, but it already knows {self.max_moves} moves.")
            print("Please choose a move to forget, or enter '0' to stop learning the new move.")
            for i, known_move in enumerate(self.moves, 1):
                print(f"{i}. {known_move.name}")
            choice = input("Enter the number of the move to forget: ")
            if choice == '0':
                print(f"{self.name} stopped learning {move.name}.")
                return False
            else:
                forgotten_move = self.moves.pop(int(choice) - 1)
                print(f"{self.name} forgot {forgotten_move.name} and learned {move.name}!")
        self.moves.append(move)
        print(f"{self.name} has learned {move.name}.")
        # Add the new move to the queue of the last 4 moves learned
        self.last_moves_learned.append(move)
        # If the length of the queue exceeds 4, remove the move at the start of the queue
        if len(self.last_moves_learned) > 4:
            self.last_moves_learned.pop(0)
        print(f"The last 4 moves learned by {self.name} are: {[move.name for move in self.last_moves_learned]}.")
        return True

    def restore_pp(self, amount):
        for move in self.moves:
            move.pp = min(move.pp + amount, 100)  # assuming max PP is 100
        print(f"All of {self.name}'s moves PP increased by {amount}!")
        return True

    def level_up_with_candy(self, moves_dict):
        self.level_up(moves_dict)
        print(f"{self.name} has leveled up to level {self.level}!")
        return True

    def apply_status_effect(self, effect):
        status_effects = {
            'paralyzed': self.paralyze,
            'frozen': self.freeze,
            'burned': self.burn,
            'poisoned': self.poison,
            'sleeping': self.sleep
        }
        status_effects[effect]()

    def check_status_effect(self):
        if self.status_effect is not None:
            effect = self.status_effect()
            if effect:
                if self.status == 'sleeping':
                    self.sleep_turns -= 1
                    if self.sleep_turns <= 0:
                        print(f"{self.name} has woken up!")
                        self.status = 'normal'
                        self.status_effect = None
                        return False
                return effect
        return False

    def is_fainted(self):
        """
        Checks if the Pokemon has fainted (i.e., its current HP is 0 or less).
        Returns True if the Pokemon has fainted and False otherwise.
        """
        print(f"Checking if {self.name} is fainted with current_health as {self.current_health}")
        return self.current_health <= 0

    def use_move(self, move, target):
        if move not in self.moves:
            print(f"{self.name} doesn't know {move.name}")
            return
        # Check if the move has enough PP
        if move.pp <= 0:
            print(f"{self.name} can't use {move.name} because it has no PP left!")
            return

        # Check if the Pokemon is paralyzed before using the move
        if self.check_status_effect():
            print(f"{self.name} can't move due to its status!")
            return

        # Define a dictionary to map the effect to the corresponding function
        effect_functions = {
            "damage": lambda: target.take_damage(self.attack * move.power/10 // target.defense, move.name),
            "heal": self.heal,
            "attack_up": lambda: self.modify_stat("attack", move.effect_magnitude),
            "defense_up": lambda: self.modify_stat("defense", move.effect_magnitude),
            "speed_up": lambda: self.modify_stat("speed", move.effect_magnitude),
            "attack_down": lambda: target.modify_stat("attack", -move.effect_magnitude),
            "defense_down": lambda: target.modify_stat("defense", -move.effect_magnitude),
            "speed_down": lambda: target.modify_stat("speed", -move.effect_magnitude),
            "paralyze": lambda: target.apply_status_effect("paralyzed"),
            "freeze": lambda: target.apply_status_effect("frozen"),
            "burn": lambda: target.apply_status_effect("burned"),
            "poison": lambda: target.apply_status_effect("poisoned"),
            "sleep": lambda: target.apply_status_effect("sleeping"),
            "status": lambda: target.apply_status_effect("not implemented"),
        }

        # Call the corresponding function based on the move's effect
        for effect in move.effects:
            if effect in effect_functions:
                effect_functions[effect]()


        # Call the corresponding function based on the move's effect
        #effect_functions[move.effect]()

        # Check if the target Pokemon has fainted
        if target.current_health <= 0:
            target.current_health = 0
            print(f"{target.name} has fainted!")

        # Print the remaining PP for the move
        print(f"{move.name} has {move.pp} PP left.")

# PokemonFactory is a class that provides a static method to create Pokemon instances.
class PokemonFactory:
    @staticmethod
    def create_pokemon(base_data, level, moves_dict):
        max_health = base_data['Max_Health'] + level  # adjust formula as needed
        attack = base_data['Attack'] + level  # adjust formula as needed
        defense = base_data['Defense'] + level  # adjust formula as needed
        speed = base_data['Speed'] + level  # adjust formula as needed

        # Get the last 4 moves that the Pokemon can learn at its current level
        learnable_moves = PokemonFactory.get_moves_at_level(base_data['Moves_to_Learn'], level, moves_dict)
        #base_data['Moves'] = learnable_moves

        evolved_form = base_data['Evolved_Form']  # no adjustment needed
        evolution_level = base_data['Evolution_Level']  # no adjustment needed
        evolution_item = base_data['Evolution_Item']  # no adjustment needed
        abilities = base_data['Abilities']  # no adjustment needed
        held_item = base_data['Held_Item']  # no adjustment needed
        region = base_data['Region']  # no adjustment needed
        sub_region = base_data['Sub_Region']  # no adjustment needed
        mana_cost = base_data['Mana_Cost']  # no adjustment needed
        rarity = base_data['Rarity']  # no adjustment needed
        price = base_data['Price']  # no adjustment needed
        description = base_data['Description']  # no adjustment needed

        pokemon_attributes = {
            'Name': base_data['Name'],
            'Index': base_data['Index'],
            'Level': level,
            'Type': base_data['Type'],
            'Max_Health': max_health,
            'Attack': attack,
            'Defense': defense,
            'Speed': speed,
            'Moves': learnable_moves,
            'Moves_to_Learn': base_data['Moves_to_Learn'],  # Add this line
            'Evolved_Form': evolved_form,
            'Evolution_Level': evolution_level,
            'Evolution_Item': evolution_item,
            'Abilities': abilities,
            'Held_Item': held_item,
            'Region': region,
            'Sub_Region': sub_region,
            'Mana_Cost': mana_cost,
            'Rarity': rarity,
            'Price': price,
            'Description': description
        }

        return Pokemon(pokemon_attributes)

    @staticmethod
    def get_moves_at_level(moves_to_learn, level, moves_dict):
        #print(f"Moves to learn: {moves_to_learn}")
        #print(f"Level: {level}")

        # Filter the moves based on the Pokemon's level
        learnable_moves = [moves_dict[move_name] for move_name, move_level in moves_to_learn.items() if move_level <= level]

        # Sort the moves based on the level at which they are learned
        learnable_moves.sort(key=lambda move: moves_to_learn[move.name], reverse=True)

        # Print the names of the learnable moves
        #print(f"Learnable moves: {[move.name for move in learnable_moves]}")

        # If the Pokemon can learn more than its maximum number of moves, only keep the last 4 moves
        if len(learnable_moves) > Pokemon.max_moves:
            learnable_moves = learnable_moves[:Pokemon.max_moves]

        return learnable_moves

class Move:
    def __init__(self, name, move_type, power, accuracy, pp, level, effects=None):
        # Initialize the attributes of the Move
        self.name = name
        self.move_type = move_type
        self.power = power
        self.accuracy = accuracy
        self.pp = pp
        self.max_pp = pp  # Add a new attribute for the maximum PP
        self.effects = effects if effects else {}  # New attribute
        self.level = level

    def __str__(self):
        # Return a string representation of the Move
        return f"{self.name} (Type: {self.move_type}, Power: {self.power}, Accuracy: {self.accuracy}, PP: {self.pp}/{self.max_pp})"

    def increase_pp(self, increase_amount):
        # Increase the maximum PP of the Move
        self.max_pp += increase_amount
        self.max_pp = int(self.max_pp)  # Convert max_pp to an integer

    def use(self, attacker, target):
        # Use the Move on a target Pokemon
        # Check if the move has PP remaining
        if self.pp <= 0:
            print(f"{attacker.name}'s move {self.name} is out of PP!")
            return False

        # Check if the move hits
        if random.randint(1, 100) <= self.accuracy:
            # Decrease PP after the move is used
            self.pp -= 1
            for effect, magnitude in self.effects.items():
                if effect == "damage":
                    attacker.use_move(self, target)
                elif effect == "heal":
                    attacker.heal(magnitude)
                elif effect == "attack_up":
                    attacker.attack += magnitude
                elif effect == "defense_up":
                    attacker.defense += magnitude
                # You can add more effects here, just define what happens when the effect is triggered
                # New effects
                elif effect == "paralyze":
                    target.apply_status_effect("paralyzed")
                elif effect == "freeze":
                    target.apply_status_effect("frozen")
                elif effect == "burn":
                    target.apply_status_effect("burned")
                elif effect == "poison":
                    target.apply_status_effect("poisoned")
                elif effect == "sleep":
                    target.apply_status_effect("sleeping")
                elif effect == "attack_down":
                    target.attack = max(1, target.attack - magnitude)
                elif effect == "defense_down":
                    target.defense = max(1, target.defense - magnitude)
        else:
            print(f"{attacker.name}'s attack missed!")

class Spell:
    def __init__(self, name, spell_type, mana_cost, price, duration, effects, effect_type, power, level, details):
        self.name = name
        self.spell_type = spell_type
        self.mana_cost = mana_cost
        self.price = price
        self.duration = duration
        self.effects = effects
        self.effect_type = effect_type
        self.power = power
        self.level = level
        self.details = details

    def __str__(self):
        return (f"{self.name} (Type: {self.spell_type}, Power: {self.power}, Mana Cost: {self.mana_cost}, "
                f"Duration: {self.duration}, Effects: {self.effects}, Effect Type: {self.effect_type})")

    def cast(self, caster, target):
        print(f"mana spent: {caster.mana_spent}")
        if self.mana_cost > caster.mana:
            print(f"current trainer mana: {caster.mana}")
            print(f"current spell mana cost: {self.mana_cost}")
            print(f"{caster.name} does not have enough mana to cast {self.name}!")
            return False
        if caster.mana_spent == False:
            caster.mana -= self.mana_cost  # Deduct the mana cost of the spell from the caster's mana


        caster.mana_spent = True
        print(f"mana: {caster.mana}")
        print(f"mana spent: {caster.mana_spent}")

        for effect, magnitude in self.effects.items():
            if effect == "damage":
                target.take_damage(magnitude)
                #caster._cast_spell(caster, self, effect, magnitude, target)
            elif effect == "heal":
                target.heal(magnitude)
            elif effect == "paralyze":
                target.apply_status_effect("paralyzed")
            # You can add more effects here, just define what happens when the effect is triggered

        return True

class Item:
    def __init__(self, name, item_type, description, effect, target, price, evolution=None, quantity=1):
        self.name = name
        self.item_type = item_type
        self.description = description
        self.effect = effect
        self.target = target
        self.price = price
        self.evolution = evolution
        self.quantity = quantity

    def use(self, trainer, pokemon=None, move=None, wild_pokemon=None, battling_wild_pokemon=None, effect=None, magnitude=None):
        print(f"Called use with pokemon: {pokemon}")
        print(f"Item effects: {self.effect}")  # Print the effects of the item
        print(f"Current wild pokemon in use method: {wild_pokemon}")  # Print the current wild pokemon

        effect_functions = trainer.get_effect_functions()

        for effect, magnitude in self.effect.items():
            if effect.lower() in effect_functions:
                # If the effect is "capture", pass wild_pokemon as an argument
                if effect.lower() == "capture":
                    if battling_wild_pokemon and wild_pokemon:
                        return effect_functions[effect.lower()] (trainer, wild_pokemon=wild_pokemon, magnitude=1, target_pokemon=wild_pokemon)
                    else:
                        print("item class use method You can't use a Pokeball here!")
                if effect.lower() == "max_revive":
                    effect_functions[effect.lower()](trainer, pokemon, magnitude)
                else:
                    # Call the function associated with the effect, and pass the parameters in the correct order.
                    effect_functions[effect.lower()](pokemon, move, wild_pokemon, magnitude)
                    print(f"Effect {effect} applied with magnitude {magnitude}")
            else:
                raise ValueError(f"Unrecognized effect: {effect}")

    def _heal(self, trainer, pokemon, move, wild_pokemon, magnitude):
        initial_health = pokemon.current_health
        pokemon.heal(int(magnitude))
        actual_healed = min(pokemon.current_health - initial_health, magnitude)
        print(f"{pokemon.name} has been healed by {actual_healed} points!")
        return True

    def _revive(self, trainer, pokemon, move, wild_pokemon, magnitude):
        return pokemon.revive()

    def _increase_pp(self, trainer, pokemon, move, wild_pokemon, magnitude):
        if move:
            move.increase_pp(magnitude)
            return True
        else:
            return False

    def _level_up(self, trainer, pokemon, move, wild_pokemon, magnitude):
        pokemon.level_up_with_candy(magnitude)
        return True

    def _evolve(self, trainer, pokemon, move, wild_pokemon, magnitude):
        if pokemon and pokemon.evolution_item == self.name:
            pokemon.evolve_with_item(self.name)
            if self.name in trainer.items:
                return True
            else:
                return False
        else:
            print(f"{pokemon.name} can't evolve using {self.name}.")
            return False

    def _capture(self, trainer, wild_pokemon=None, magnitude=None):
        print("Entering _capture method.")
        print(f"Current wild pokemon in _capture method: {wild_pokemon}")  # Print the current wild pokemon

        if wild_pokemon:
            capture_probability = 1 - (wild_pokemon.current_health / wild_pokemon.max_health)
            if wild_pokemon.status != 'normal':
                capture_probability *= 1.5
            if random.random() < capture_probability:
                print(f"You have successfully captured {wild_pokemon.name}!")
                if len(trainer.pokemon_list) < 6:
                    trainer.add_pokemon(wild_pokemon)
                    print(f"{wild_pokemon.name} has been added to your team!")
                    raise PokemonCaptured
                else:
                    trainer.storage.append(wild_pokemon)
                    print(f"Your team is full! {wild_pokemon.name} has been sent to storage.")
                    raise PokemonCaptured
                return True
            else:
                print(f"{wild_pokemon.name} broke free!")
                return False
        else:
            print("capture You can't use a Pokeball here!")
            return False

    def _increase_speed(self, trainer, pokemon, move, wild_pokemon, magnitude):
        return pokemon.increase_speed(magnitude)

    def _increase_critical_hit_ratio(self, trainer, pokemon, move, wild_pokemon, magnitude):
        return pokemon.increase_critical_hit_ratio(magnitude)

    def _prevent_stat_lower(self, trainer, pokemon, move, wild_pokemon, magnitude):
        return pokemon.prevent_stat_lower()

    def _teach_move(self, trainer, pokemon, move, wild_pokemon, magnitude):
        return pokemon.learn_move(move)

class Potion(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon=None, move=None, wild_pokemon=None, magnitude=None):
        initial_health = pokemon.current_health
        heal_amount = self.effect["heal"]
        pokemon.current_health += heal_amount
        if pokemon.current_health > pokemon.max_health:
            pokemon.current_health = pokemon.max_health
        actual_heal_amount = pokemon.current_health - initial_health
        print(f'{pokemon.name} was healed for {actual_heal_amount} HP!')
        return True
class Revive(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon=None, move=None, wild_pokemon=None, magnitude=None):
        if pokemon.revive():  # Call the revive method directly
            print(f'{pokemon.name} has been revived!')
            return True
        else:
            print(f"{pokemon.name} is not fainted and can't be revived.")
            return False
class EvolutionStone(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon=None, move=None, wild_pokemon=None, magnitude=None):
        if pokemon.evolution_item == self.name:  # Check if the Pokémon can evolve with this stone
            return pokemon.evolve_with_item(self.name)
        else:
            print(f"{pokemon.name} can't evolve using {self.name}.")
            return False
class Antidote(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon=None, move=None, wild_pokemon=None, magnitude=None):
        return pokemon.cure_poison()
class Awakening(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon=None, move=None, wild_pokemon=None, magnitude=None):
        return pokemon.cure_sleep()
class ParalyzeHeal(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon=None, move=None, wild_pokemon=None, magnitude=None):
        return pokemon.cure_paralysis()
class PPUp(Item):
    def __init__(self, name, item_type, description, effect, target, price, rarity):
        super().__init__(name, item_type, description, effect, target, price, rarity)

    def use(self, trainer, pokemon=None, move=None, wild_pokemon=None, magnitude=None):
        if move:
            print(f"You will use the item on {move.name}!")
            if move.pp < 50:
                increase_amount = int(move.max_pp * self.effect["increase_pp"])
                move.max_pp += increase_amount
                move.pp += increase_amount  # Increase the current PP as well
                move.pp = min(move.pp, move.max_pp)  # Ensure that PP does not exceed max PP
                print(f"{move.name}'s PP has been increased to {move.pp}!")
                return True
            else:
                print(f"{move.name}'s PP is already at maximum!")
                return False
        else:
            print("This item cannot be used to increase PP.")
            return False
class HpUp(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon=None, move=None, wild_pokemon=None, magnitude=None):
        return pokemon.increase_max_health(self.effect["increase_max_health"])
class XAccuracy(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon=None, move=None, wild_pokemon=None, magnitude=None):
        return pokemon.increase_accuracy(self.effect["increase_accuracy"])
class XAttack(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon=None, move=None, wild_pokemon=None, magnitude=None):
        return pokemon.increase_attack(self.effect["increase_attack"])
class XDefense(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon=None, move=None, wild_pokemon=None, magnitude=None):
        return pokemon.increase_defense(self.effect["increase_defense"])
class Ether(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon=None, move=None, wild_pokemon=None, magnitude=None):
        return pokemon.restore_pp(self.effect["restore_pp"])
class BurnHeal(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon=None, move=None, wild_pokemon=None, magnitude=None):
        return pokemon.cure_burn()
class RareCandy(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon=None, move=None, wild_pokemon=None, magnitude=None):
        if pokemon:
            return pokemon.level_up_with_candy(magnitude)  # Call the level_up_with_candy method of the Pokemon class
        else:
            return False
class Pokeball(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon=None, move=None, wild_pokemon=None, battling_wild_pokemon=None, magnitude=None):
        if battling_wild_pokemon and wild_pokemon:
            return super().use(trainer, battling_wild_pokemon, wild_pokemon)
        else:
            print("pokeball class You can't use a Pokeball here!")
class FullRestore(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon, move=None, wild_pokemon=None):
        super().use(trainer, pokemon)
        pokemon.cure_status()  # Assuming you have a method in Pokemon class to cure all status conditions
class MaxPotion(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon, move=None, wild_pokemon=None):
        super().use(trainer, pokemon)
class MaxRevive(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon, move=None, wild_pokemon=None):
        super().use(trainer, pokemon)
class Elixir(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon, move=None, wild_pokemon=None):
        for move in pokemon.moves:  # Assuming pokemon.moves is a list of Move objects
            super().use(trainer, pokemon, move)
class MaxElixir(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon, move=None, wild_pokemon=None):
        for move in pokemon.moves:
            super().use(trainer, pokemon, move)
class XSpeed(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon, move=None, wild_pokemon=None):
        pokemon.increase_speed(self.effect["increase_speed"])  # Assuming you have a method in Pokemon class to increase speed
class DireHit(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon, move=None, wild_pokemon=None):
        pokemon.increase_critical_hit_ratio(self.effect["increase_critical_hit_ratio"])  # Assuming you have a method in Pokemon class to increase critical hit ratio
class GuardSpec(Item):
    def __init__(self, name, item_type, description, effect, target, price):
        super().__init__(name, item_type, description, effect, target, price)

    def use(self, trainer, pokemon, move=None, wild_pokemon=None):
        pokemon.prevent_stat_lower()  # Assuming you have a method in Pokemon class to prevent stats from being lowered

class TMHM(Item):
    def __init__(self, name, move):
        super().__init__(name=name, item_type="TM", description=f"Teaches a Pokémon the move {move.name}.", effect={"teach_move": 1}, target={"choose_own_pokemon"}, price=5000)
        self.move = move
        
    def use(self, trainer, pokemon, move=None, wild_pokemon=None):
        if pokemon.learn_move(self.move):
            print(f"{pokemon.name} has learned {self.move.name}!")
            return True
        else:
            print(f"{pokemon.name} can't learn {self.move.name}.")
            return False      

class Trainer:
    def __init__(self, name, pokemon_list=None, is_human=False, items=None, coins=0, team=None, region=None, sub_region=None, spells=None, mana=0, max_health=0, tm_chart=None,spells_chart=None, moves_dict=None):
        self.name = name
        self.pokemon_list = pokemon_list[:6] if pokemon_list else []  # Limit the team to 6 Pokemon
        self.tm_chart = tm_chart if tm_chart else {}
        self.spells_chart = spells_chart if spells_chart else {}
        self.storage = pokemon_list[6:] if pokemon_list else []  # Store the extra Pokemon
        self.is_human = is_human
        self.items = list(items.values()) if items else []
        self.coins = coins
        self.team = team
        self.region = region
        self.sub_region = sub_region
        self.spells = spells
        self.mana = mana
        self.max_mana = mana
        self.max_health = max_health
        self.current_health = max_health
        self.current_pokemon = None
        self.item_used = False
        self.moves_dict = moves_dict if moves_dict else {}  # Initialize moves_dict
        self.opponent = None
        self.battling_wild_pokemon = False  # Add this line
        self.active_pokemon = None
        self.mana_spent = False

        # Set the first pokemon as the current pokemon if the list is not empty
        if self.pokemon_list:
            self.current_pokemon = self.pokemon_list[0]

        # Property to access active_pokemon
    @property
    def active_pokemon(self):
        return self._active_pokemon
    # Setter method for active_pokemon
    @active_pokemon.setter
    def active_pokemon(self, pokemon):
        self._active_pokemon = pokemon
    # Add these methods
    def start_battle_with_wild_pokemon(self):
        # This method sets the battling_wild_pokemon attribute to True, indicating that the trainer is currently battling a wild Pokemon.
        print("START BATTLE WITH WILD POKEMON")
        self.battling_wild_pokemon = True

    def end_battle_with_wild_pokemon(self):
        # This method sets the battling_wild_pokemon attribute to False, indicating that the trainer is no longer battling a wild Pokemon.
        self.battling_wild_pokemon = False

    def choose_action(self, wild_pokemon=None, opponent_pokemon=None):
        while True:
            action = self.get_action()
            if action == '1':
                return self.perform_move_action()
            elif action == '2':
                return self.perform_switch_action()
            elif action == '3':
                item, quantity = self.choose_item()
                if item is not None:
                    return self.perform_item_action(item, quantity, wild_pokemon)
            elif action == '4':
                return self.perform_exit_action()
            elif action == '5':
                return self.perform_info_action()
            elif action == '6':  # New action for Pokemon Attack
                action, target = self.perform_attack_action(opponent_pokemon)
                return action, target
            else:
                print("Invalid choice. Please try again.")

    def get_action(self):
        if self.is_human:
            print(f"{self.name}, what would you like to do?")
            print("1. Move\n2. Switch\n3. Use item\n4. Exit game\n5. Get info\n6. Pokemon Attack")  # Added new option
            return input("Choose an action: ")
        else:
            # Use the auto_choose_action method for the AI
            action, target = self.auto_choose_action()
            return action

    def perform_attack_action(self, opponent_pokemon):
        if opponent_pokemon is not None:
            damage = (self.current_pokemon.attack / opponent_pokemon.defense) * 10
            damage = round(damage)  # Round the damage to a whole number
            opponent_pokemon.current_health = max(0, opponent_pokemon.current_health - damage)
            print(f"{self.current_pokemon.name} attacked {opponent_pokemon.name} for {damage} damage!")
            print(f"{opponent_pokemon.name} now has {opponent_pokemon.current_health} health remaining.")
            return "attack", None  # Return a tuple indicating the action and that there is no specific target
        else:
            print("There is no opponent Pokemon to attack.")
            return None, None

    def perform_move_action(self):
        move = self.choose_move(self.current_pokemon)
        if move is not None:
            return ("move", move)
        else:
            return None, None  # Return a tuple of None values

    def perform_switch_action(self):
        new_pokemon = self.choose_pokemon()
        if new_pokemon:
            return ("switch", new_pokemon)
        else:
            print("You can't switch Pokemon as you only have one. Please choose another action.")
            return None, None  # Return a tuple of None values

    def perform_item_action(self, item, quantity, wild_pokemon):
        # Check if the item is a Pokeball
        if item.name == 'Pokeball':
            # Check if the battle is against a wild Pokemon
            if wild_pokemon is not None:
                # Call the capture method directly if it's a Pokeball and the battle is against a wild Pokemon
                self.capture(wild_pokemon, item)
                # End the turn after attempting to capture
                return True, None
            else:
                # Print a message informing the user that they cannot use a Pokeball in a trainer battle
                print("You can't use a Pokeball in a trainer battle!")
                return False, None
        else:
            # Check the target of the item
            if item.target == 'choose_own_pokemon':
                target = PygameBattle.choose_pokemon_pygame(item.name)
                print(f"choose_own_pokemon perform_item_action Target: {target} item.target: {item.target}")
            elif item.target == 'choose_opp_pokemon':
                target = PygameBattle.choose_opponent_pokemon_pygame()
                print(f"choose_opp_pokemon perform_item_action Target: {target} item.target: {item.target}")
            elif item.target == 'opp_trainer':
                target = self.opponent
                print(f"opp_trainer perform_item_action Target: {target} item.target: {item.target}")
            elif item.target == 'human_trainer':
                target = self  # Assuming that 'self' is the human trainer
                print(f"human_trainer perform_item_action Target: {target} item.target: {item.target}")
            elif item.target == 'all_own_pokemon':
                target = self.pokemon_list  # All Pokémon belonging to the human trainer
                print(f"all_own_pokemon perform_item_action Target: {target} item.target: {item.target}")
            elif item.target == 'all_opp_pokemon':
                target = self.opponent.pokemon_list  # All Pokémon belonging to the opponent trainer
                print(f"all_opp_pokemon perform_item_action Target: {target} item.target: {item.target}")
            else:
                target = self.current_pokemon
                print(f"else perform_item_action Target: {target} item.target: {item.target}")

            print(f"perform_item_action Target: {target}")

            # Call choose_move only if the item is "Ether" or "PP Up"
            move_to_use_on = None
            if item.name in ["Ether", "PP Up"]:
                move_to_use_on = self.choose_move(target, item_use=True)

            if self.use_item(target, item, quantity, move_to_use_on, wild_pokemon=wild_pokemon, battling_wild_pokemon=self.battling_wild_pokemon):
                print(f"Selected item in perform_item_action: {item}")
                self.item_used = True
                return None, None
            else:
                if len(self.items) == 0:
                    print("You have no items to use. Please choose another action.")

    def perform_exit_action(self):
        print(f"{self.name} decided to exit the battle.")
        raise ExitBattle

    def perform_info_action(self):
        print(self.current_pokemon)
        return None, None

    def auto_choose_action(self):
        # Check how many items the trainer has
        total_items = len(self.items)  # Use len() for a list
        print(f"Total items: {total_items}")

        # Count the number of potions the trainer has
        total_potions = sum(int(item.split(':')[1]) for item in self.items if 'Potion' in item)
        print(f"Total potions: {total_potions}")


        # Check the HP of the current Pokemon
        current_hp = self.current_pokemon.current_health
        max_hp = self.current_pokemon.max_health
        print(f"Current HP: {current_hp}, Max HP: {max_hp}")

        # Check how many PP are remaining for each move
        pp_remaining = [move.pp for move in self.current_pokemon.moves]
        print(f"PP remaining for each move: {pp_remaining}")

        # Check if any move has PP remaining
        has_pp_remaining = any(pp > 0 for pp in pp_remaining)
        print(f"Any move has PP remaining: {has_pp_remaining}")

        # Decision making logic

        #implement ai item use
        """if current_hp < max_hp * 0.3 and total_items > 0:
            # If current HP is below 30% and the trainer has items, use an item
            action = "item"
            target = None  # You can specify the item to use here
            print("Decision: Use an item")

            # Actually use the item
            self.items.pop()  # This assumes items are stored in a list and any item can be used
            total_items -= 1  # Decrease the number of items
            self.current_pokemon.current_health += 20  # This assumes using an item increases HP by 20
            current_hp = self.current_pokemon.current_health  # Update current HP"""
        
        if has_pp_remaining:
            # If the current Pokemon has PP remaining for any move, choose a move
            action = "move"
            # Choose the move with the highest PP remaining
            index_of_move_with_max_pp = pp_remaining.index(max(pp_remaining))
            target = self.current_pokemon.moves[index_of_move_with_max_pp]
            print("Decision: Use a move")
        else:
            # If no move has PP remaining, use Pokemon Attack
            action = "attack"
            target = None
            print("Decision: Use Pokemon Attack")

        return action, target

    def capture(self, wild_pokemon, item):
        print("Inside capture method...")
        # This method attempts to capture a wild Pokemon. The chance of success depends on the Pokemon's current health and status.
        # The capture rate is calculated as the proportion of the Pokemon's health that has been lost.
        capture_rate = (wild_pokemon.max_health - wild_pokemon.current_health) / wild_pokemon.max_health
        print(f"Initial capture rate based on health: {capture_rate:.2f}")

        # If the Pokemon has a status condition, the capture rate is increased by 25%.
        if wild_pokemon.status != "normal":
            capture_rate += 0.25
            print(f"Capture rate increased due to status condition: {capture_rate:.2f}")
            print(f"Wild Pokemon's status: {wild_pokemon.status}")

        # Generate a random number for the capture attempt
        random_number = random.random()
        print(f"Random number for capture attempt: {random_number:.2f}")

        # If the random number is less than the capture rate, the capture is successful.
        if random_number < capture_rate:
            print(f"{self.name} captured {wild_pokemon.name}!")
            # The captured Pokemon is added to the trainer's list of Pokemon.
            if len(self.pokemon_list) < 6:
                self.pokemon_list.append(wild_pokemon)
                print(f"{wild_pokemon.name} has been added to your team!")
            else:
                self.storage.append(wild_pokemon)
                print(f"Your team is full! {wild_pokemon.name} has been sent to storage.")
            # Call _finalize_item_use to decrement the Pokeball quantity
            self._finalize_item_use(item, [True])
            raise PokemonCaptured  # Raise the exception when the Pokemon is captured
            #return True, wild_pokemon  # Return True when the Pokemon is captured
        else:
            # If the capture is unsuccessful, a message is printed to inform the player.
            print(f"{wild_pokemon.name} escaped!")
            # Call _finalize_item_use to decrement the Pokeball quantity even if the capture was unsuccessful
            self._finalize_item_use(item, [False])
            return False, None  # Return False when the Pokemon is not captured

    def add_item(self, item, quantity=1):
        for i, (item_object, existing_quantity) in enumerate(self.items):
            if item_object.name == item.name:
                self.items[i][1] += quantity  # Increase the quantity of the existing item
                break
        else:  # If the item is not already in the list, add a new instance
            self.items.append([item, quantity])

    def choose_item(self):
        print(f"{self.name}'s items:")


        if isinstance(self.items, dict):
            items = list(self.items.items())
        elif isinstance(self.items, list):
            items = self.items
        else:
            print(f"Unexpected type for self.items: {type(self.items)}")
            return None, None

        for i, item in enumerate(items):
            print(f"{i + 1}. {item.name}: {item.quantity}")

        choice = int(input("Choose an item: ")) - 1
        if choice == -1:
            return None, None  # Return a tuple of None values if the player chose to go back
        if choice < 0 or choice >= len(items):
            print("Invalid choice. Please enter a number corresponding to an item.")
            return None, None

        selected_item = items[choice]
        print(f"Selected item: {selected_item.name}, Effect: {selected_item.effect}, Target: {selected_item.target}")

        if selected_item.quantity > 0:
            if selected_item.effect == "catch" and not self.battling_wild_pokemon:
                print("You can't use a Pokeball here!")
                return None, None
            return selected_item, selected_item.quantity
        else:
            print(f"You don't have any more {selected_item.name}s!")
            return None, None

    # Modify your use_item method in the Trainer class
    def use_item(self, target_func, target, item, quantity, spells_chart, move_to_use_on=None, wild_pokemon=None, battling_wild_pokemon=None):
        print(f"Item at the beginning of use_item: {item.name}")
        print(f"use_item wild_pokemon: {wild_pokemon}")
        target = target_func()  # Call the target_func to get the actual target
        current_target = target

        if item.name=='Pokeball':
            wild_pokemon = current_target

        if not self._validate_item_and_pokemon(item, target):
            return False

        if quantity <= 0:
            print(f"You have no {item.name}s left.")
            return False

        effect_functions = self.get_effect_functions()

        print(f"use_item Target: {target.name}")

        success = []
        if isinstance(target, list):
            
            print("pokemon team target use_item")
            # target is a list of Pokemon instances
            for pokemon in target:
                if isinstance(item.effect, dict):
                    success.append(self._handle_item_with_multiple_effects(item, effect_functions, pokemon, spells_chart, wild_pokemon, battling_wild_pokemon))
                else:
                    success.append(self._handle_item_with_single_effect(item, effect_functions, pokemon))
            return self._finalize_item_use(item, success)  # Add this line to return from the method if target is a list
        elif isinstance(target, Pokemon):
            print("pokemon target use_item")
            if isinstance(item.effect, dict):
                success = self._handle_item_with_multiple_effects(item, effect_functions, target, spells_chart, wild_pokemon, battling_wild_pokemon)
            else:
                success = self._handle_item_with_single_effect(item, effect_functions, target)
        elif isinstance(target, Move):  # Add this block to handle when the target is a move.
            print("move target use_item")
            if isinstance(item.effect, dict):
                success = self._handle_item_with_multiple_effects(item, effect_functions, target, spells_chart, wild_pokemon=wild_pokemon)
            else:
                success = self._handle_item_with_single_effect(item, effect_functions, target)
        elif isinstance(target, Trainer):
            print("trainer target use_item")
            if isinstance(item.effect, dict):
                print(f"trainer target use_item: {item.effect}")
                success = self._handle_item_with_multiple_effects(item, effect_functions, target, spells_chart, wild_pokemon, battling_wild_pokemon)
            else:
                success = self._handle_item_with_single_effect(item, effect_functions, target)
        else:
            print(f"target: {target}")
            print(f"trainer target use_item: {item.effect}")
            print("Invalid target for item use.")
            return False

        print(f"Success before capturing: {success}")
        print("Finalizing item use without capturing...")
        return self._finalize_item_use(item, success)

    def _validate_item_and_pokemon(self, item, target):
        if not target:
            print("Please choose a Pokemon to use the item on.")
            return False

        if not item:
            print("Please choose a valid item.")
            return False

        if not self.current_pokemon:
            print("You don't have a current Pokémon. Please switch to a Pokémon before using an item.")
            return False

        return True

    def get_effect_functions(self):
        
        return {
            "evolve": self._use_item_generic,
            "level_up": self._use_item_generic,
            "increase_pp": self._use_ppup,
            "heal": self._use_item_generic,
            "revive": self._use_item_generic,
            "cure_poison": self._use_antidote,
            "capture": self.capture,
            "max_revive": self._use_item_generic,
            "increase_hp": self._use_hpup,
            "increase_accuracy": self._use_x_accuracy,
            "increase_attack": self._use_x_attack,
            "increase_defense": self._use_x_defense,
            "restore_pp": self._use_ether,
            "cure_burn": self._use_burn_heal,
            "cure_paralysis": self._use_paralyze_heal,
            "cure_sleep": self._use_awakening,
            "increase_critical_hit_ratio": self._use_dire_hit,
            "prevent_stat_lower": self._use_guard_spec,
            "increase_speed": self._use_x_speed,
            "full_restore": self._use_full_restore,
            "max_heal": self._use_max_potion,
            "restore_pp_all": self._use_elixir,
            "restore_pp_all_max": self._use_max_elixir,
            "teach_move": self._use_teach_move,
            "cast_spell": self._cast_spell,
            "trainer_heal": self.trainer_heal,
            "trainer_damage": self.trainer_damage
        }

    """def _handle_item_with_multiple_effects(self, item, effect_functions, pokemon, wild_pokemon, battling_wild_pokemon):
        success = []
        for effect, magnitude in item.effect.items():
            if effect in effect_functions:
                if effect.lower() == 'capture':
                    if item.name == "Pokeball":
                        # Only call capture if the item used is a Pokeball
                        success.append(effect_functions[effect.lower()](wild_pokemon))
                    else:
                        print(f"Cannot capture with {item.name}.")
                        return [False]
                elif effect.lower() == 'teach_move':
                    print(f"TM Chart: {self.tm_chart}")
                    # Pass the trainer, pokemon, item, effect, and magnitude here for the teach_move effect
                    success.append(effect_functions[effect.lower()](self, pokemon, item, effect, magnitude, wild_pokemon=wild_pokemon))
                
                
                elif effect.lower() == 'cast_spell':    
                    # Get the actual Spell instance 
                    #spell_name = item.name
                    #print(f"Spells Chart: {self.spells_chart}")
                    #spell = self.spells_chart[spell_name]
                    # Pass magnitude and target_pokemon here
                    #if item.target == 'choose_opp_pokemon':
                    #    target_pokemon = self.choose_opponent_pokemon()
                    #    if target_pokemon is None:
                    #        return [False]
                    success.append(effect_functions[effect.lower()](self, item, effect, magnitude, self.opponent.current_pokemon))
                else:
                    # Pass the effect and magnitude here for other effects
                    success.append(effect_functions[effect.lower()](pokemon, item, effect, magnitude, wild_pokemon=wild_pokemon))
            else:
                print(f"The effect of {item.name} is not implemented yet.")
                return [False]
        return success"""

    def _handle_item_with_multiple_effects(self, item, effect_functions, target, spells_chart, wild_pokemon=None, battling_wild_pokemon=None):
        success = []
        print(f"_handle_item_with_multiple_effects target: {target.name}")
        print(f"_handle_item_with_multiple_effects wild_pokemon: {wild_pokemon}")
        
        for effect, magnitude in item.effect.items():
            if effect in effect_functions:
                if isinstance(target, Move):
                    # Handle the Move target case
                    success.append(effect_functions[effect.lower()](self.current_pokemon, item, effect, magnitude, spells_chart, move=target, wild_pokemon=wild_pokemon))

                if isinstance(target, Pokemon):
                    # Inside _handle_item_with_multiple_effects
                    if effect.lower() == 'capture':
                        if item.name == "Pokeball":
                            # Only call capture if the item used is a Pokeball
                            success.append(effect_functions[effect.lower()](wild_pokemon, item))  # Pass both wild_pokemon and item
                        else:
                            print(f"Cannot capture with {item.name}.")
                            return [False]
                    elif effect.lower() == 'teach_move':
                        print(f"TM Chart: {self.tm_chart}")
                        # Pass the trainer, pokemon, item, effect, and magnitude here for the teach_move effect
                        success.append(effect_functions[effect.lower()](self, target, item, effect, magnitude, wild_pokemon=wild_pokemon))
                    
                    elif effect.lower() == 'cast_spell':    
                        print("elif effect.lower() == 'cast_spell': ")
                        # Get the actual Spell instance 
                        #spell_name = item.name
                        #print(f"Spells Chart: {self.spells_chart}")
                        #spell = self.spells_chart[spell_name]
                        # Pass magnitude and target_pokemon here
                        #if item.target == 'choose_opp_pokemon':
                        #    target_pokemon = self.choose_opponent_pokemon()
                        #    if target_pokemon is None:
                        #        return [False]
                        success.append(effect_functions[effect.lower()](self, item, effect, magnitude, target, spells_chart))
                    else:
                        # Pass the effect and magnitude here for other effects
                        success.append(effect_functions[effect.lower()](target, item, effect, magnitude, spells_chart, wild_pokemon=wild_pokemon))
                elif isinstance(target, Trainer):
                    print(f"_cast_spell target: {target.name}")
                    print("trainer target multiple effects")
                    if effect.lower() == 'cast_spell':    
                        # Get the actual Spell instance 
                        #spell_name = item.name
                        #print(f"Spells Chart: {self.spells_chart}")
                        #spell = self.spells_chart[spell_name]
                        # Pass magnitude and target_pokemon here
                        #if item.target == 'choose_opp_pokemon':
                        #    target_pokemon = self.choose_opponent_pokemon()
                        #    if target_pokemon is None:
                        #        return [False]
                        success.append(effect_functions[effect.lower()](self, item, effect, magnitude, target, spells_chart))
                    else:
                        # Pass the effect and magnitude here for other effects
                        success.append(effect_functions[effect.lower()](target, item, effect, magnitude, spells_chart, wild_pokemon=wild_pokemon))
            else:
                print(f"The effect of {item.name} is not implemented yet.")
                return [False]
        return success

    def _handle_item_with_single_effect(self, item, effect_functions, target):
        print(f"Item at the beginning of single effect: {item}")
        if item.effect in effect_functions:
            # Pass the item object here
            return [effect_functions[item.effect](target, item)]
        else:
            print(f"The effect of {item.name} is not implemented yet.")
            return [False]

    def _finalize_item_use(self, item, success):
        print(f"Inside _finalize_item_use, success: {success}")
        # Update the item quantity whether the action is successful or not
        #self.update_item_quantity(item)
        self.item_used = True
        if True in success:
            print("Item use was successful.")
        else:
            print("Item use completed without success.")
        return True

    def _use_item_generic(self, pokemon, item, effect, magnitude, spells_chart, move=None, wild_pokemon=None):
        if item is None:
            print("Error: item is None")
            return False
        # Add this block to handle the 'heal' effect
        elif effect == "heal":
            pokemon.current_health = min(pokemon.current_health + magnitude, pokemon.max_health)
            print(f"{pokemon.name}'s health was restored by {magnitude} points!")
        # Apply the effect directly.
        if effect == "level_up":
            pokemon.level += magnitude
            print(f"{pokemon.name} leveled up by {magnitude}!")
        elif effect == "revive":
            if pokemon.current_health == 0:
                pokemon.current_health = magnitude
                print(f"{pokemon.name} has been revived with {magnitude} HP!")
            else:
                print(f"{pokemon.name} is not fainted and can't be revived.")
                return False
        elif effect == "max_revive":
            if pokemon.current_health == 0:
                pokemon.current_health = pokemon.max_health
                print(f"{pokemon.name} has been revived with {magnitude} HP!")
            else:
                print(f"{pokemon.name} is not fainted and can't be revived.")
                return False
        elif effect == "cure_status":
            if pokemon.status == magnitude:
                pokemon.status = None
                print(f"{pokemon.name} was cured of {magnitude}!")
            else:
                print(f"{pokemon.name} is not {magnitude}.")
                return False
        elif effect == "increase_stat":
            if magnitude in ["attack", "defense", "speed", "accuracy", "critical_hit_ratio"]:
                setattr(pokemon, magnitude, getattr(pokemon, magnitude) + 1)
                print(f"{pokemon.name}'s {magnitude} increased!")
            else:
                print("Invalid stat increase.")
                return False
        elif effect == "prevent_stat_lower":
            pokemon.prevent_stat_lower = True
            print(f"{pokemon.name}'s stats will not be lowered for the next 5 turns!")
        elif effect == "restore_hp":
            pokemon.current_health = min(pokemon.current_health + magnitude, pokemon.max_health)
            print(f"{pokemon.name}'s health was restored by {magnitude} points!")
        elif effect == "increase_max_hp":
            pokemon.max_health += magnitude
            print(f"{pokemon.name}'s maximum health increased by {magnitude} points!")
        elif effect == "restore_pp":
            if move:
                move.pp = min(move.pp + magnitude, move.max_pp)
                print(f"{move.name}'s PP was restored by {magnitude} points!")
            else:
                print("Please choose a valid move.")
                return False
        elif effect == "restore_pp_all":
            for move in pokemon.moves:
                move.pp = min(move.pp + magnitude, move.max_pp)
                print(f"{move.name}'s PP was restored by {magnitude} points!")
        elif effect == "increase_pp":
            if move:
                move.max_pp = move.max_pp + int(move.max_pp * magnitude)
                print(f"{move.name}'s maximum PP increased by {int(move.max_pp * magnitude)}!")
            else:
                print("Please choose a valid move.")
                return False
        else:
            print(f"Error: Unknown effect '{effect}'")
            return False

        return True

    def _use_ppup(self, pokemon, item, effect, magnitude, spells_chart, move=None, wild_pokemon=None):
        if move:
            # Increase the maximum PP of the move by the specified magnitude (e.g., 20%)
            move.max_pp += int(move.max_pp * magnitude)
            # Make sure the current PP is not greater than the new maximum PP
            move.pp = min(move.pp, move.max_pp)
            return True
        else:
            print("Please choose a valid move.")
            return False

    """def _use_revive(self, pokemon, item, effect, magnitude, wild_pokemon=None):
        if pokemon.current_health == 0:
            return item.use(trainer, pokemon)
        print(f"{pokemon.name} is not fainted and can't be revived.")
        return False"""

    def _use_max_revive(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        if pokemon.current_health == 0:
            pokemon.current_health = pokemon.max_health
            return True
        print(f"{pokemon.name} is not fainted and can't be revived.")
        return False

    def _use_antidote(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        if pokemon.status == "poisoned":
            return item.use(pokemon)
        print(f"{pokemon.name} is not poisoned and can't be cured.")
        return False

    def _use_hpup(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        if "increase_hp" in item.effect:
            pokemon.max_health += item.effect["increase_hp"]
            return True
        else:
            print(f"{item.name} cannot be used to increase max health.")
            return False

    def _use_ether(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        move_to_use_on = self.choose_move(pokemon, item_use=True)
        if move_to_use_on is None:
            print("Please choose a valid move.")
            return False
        if move_to_use_on.pp < move_to_use_on.max_pp:
            move_to_use_on.pp = min(move_to_use_on.pp + item.effect["restore_pp"], move_to_use_on.max_pp)
            return True
        else:
            print(f"{move_to_use_on.name} already has full PP.")
            return False

    def _use_x_accuracy(self, pokemon, item, effect, magnitude, spells_chart, move=None, wild_pokemon=None):
        print(f"_use_x_accuracy selected move: {move}")
        if move:
            move.accuracy += item.effect["increase_accuracy"]
            return True
        else:
            print("No move selected for X Accuracy use.")
            return False

    def _use_x_attack(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        pokemon.attack += item.effect["increase_attack"]
        return True

    def _use_x_defense(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        pokemon.defense += item.effect["increase_defense"]
        return True

    def _use_restore_pp(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        for move in pokemon.moves:
            move.pp += item.effect["restore_pp"]
        return True

    def _use_burn_heal(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        if pokemon.status == "burned":
            pokemon.status = None
            print(f"{pokemon.name} was cured of its burn!")
            return True
        else:
            print(f"{pokemon.name} is not burned.")
            return False

    def _use_paralyze_heal(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        if pokemon.status == "paralyzed":
            pokemon.status = None
            print(f"{pokemon.name} was cured of its paralysis!")
            return True
        else:
            print(f"{pokemon.name} is not paralyzed.")
            return False

    def _use_cure_paralysis(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        if pokemon.status == "paralyzed":
            pokemon.status = None
            return True
        return False

    def _use_awakening(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        if pokemon.status == "sleep":
            pokemon.status = None
            print(f"{pokemon.name} has woken up!")
            return True
        else:
            print(f"{pokemon.name} is not asleep.")
            return False

    def _use_cure_sleep(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        if pokemon.status == "sleep":
            pokemon.status = None
            return True
        return False

    def _use_dire_hit(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        pokemon.critical_hit_ratio += item.effect["increase_critical_hit_ratio"]
        print(f"{pokemon.name}'s critical hit ratio increased!")
        return True

    def _use_increase_critical_hit_ratio(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        pokemon.critical_hit_ratio += item.effect["increase_critical_hit_ratio"]
        return True

    def _use_guard_spec(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        pokemon.prevent_stat_lower = True
        print(f"{pokemon.name}'s stats will not be lowered for the next 5 turns!")
        return True

    def _use_x_speed(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        pokemon.speed += item.effect["increase_speed"]
        print(f"{pokemon.name}'s speed increased!")
        return True

    def _use_prevent_stat_lower(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        pokemon.prevent_stat_lower = True
        return True

    def _use_increase_speed(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        pokemon.speed += item.effect["increase_speed"]
        return True

    def _use_full_restore(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        pokemon.current_health = pokemon.max_health
        pokemon.status = None
        return True

    def _use_max_heal(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        pokemon.current_health = pokemon.max_health
        return True

    def _use_restore_pp_all(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        for move in pokemon.moves:
            move.pp = move.max_pp
        return True

    def _use_max_potion(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        if pokemon.current_health < pokemon.max_health:
            pokemon.current_health = pokemon.max_health
            print(f"{pokemon.name}'s health was fully restored!")
            return True
        else:
            print(f"{pokemon.name}'s health is already full.")
            return False

    def _use_elixir(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        for move in pokemon.moves:
            if move.pp < move.max_pp:
                move.pp += item.effect["restore_pp_all"]
                if move.pp > move.max_pp:
                    move.pp = move.max_pp
                print(f"{move.name}'s PP was restored by {item.effect_magnitude} points!")
        return True

    def _use_max_elixir(self, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        for move in pokemon.moves:
            move.pp = move.max_pp
            print(f"{move.name}'s PP was fully restored!")
        return True

    def _use_teach_move(self, trainer, pokemon, item, effect, magnitude, spells_chart, wild_pokemon=None):
        # Check if the item is a TMHM
        if isinstance(item, TMHM):
            # Extract the TM number from the item's name
            tm_number = item.name.split(' ')[0]  # Assuming the name is in the format 'TMxx (Move Name)'
            # Use the TMHM on the Pokemon
            if tm_number in self.tm_chart:
                move = self.tm_chart[tm_number]
                # Print the type of the move and the type of the Pokemon
                print(f"Move type: {move.move_type}")
                print(f"Pokemon type: {pokemon.ptype}")
                # Check if the move's type matches the Pokemon's type
                if move.move_type not in pokemon.ptype and move.move_type != "Normal":
                    # Inform the player that the Pokemon cannot learn the move
                    print(f"{pokemon.name} cannot learn {move.name} because the move's type does not match the Pokemon's type.")
                    # Return False to indicate that the item use was not successful
                    return False
                return item.use(trainer, pokemon, move)
            else:
                print(f"{tm_number} is not a valid TM number.")
                return False
        else:
            print("This item cannot be used to teach a move.")
            return False
            
    def _cast_spell(self, trainer, item, effect, magnitude, target, spells_chart):
        #print(f"spells_chart: {spells_chart}")
        # Check if the item's effect is 'cast_spell'
        if effect == 'cast_spell':
            # Extract the Spell name from the item's name
            spell_name = item.name
            print(f"Spell Name: {spell_name} _cast_spell")
            print(f"_cast_spell target: {target.name}")

            if isinstance(target, list):
                # If target is a list, loop over all Pokemon in the list
                success = []
                for pokemon in target:
                    success.append(self._apply_spell_to_pokemon(trainer, spell_name, pokemon, spells_chart))
                return success
            elif isinstance(target, Trainer):
                print("trainer target cast spell")
                # Get the Spell object corresponding to the spell name
                print(f"Trainer object: {trainer}")
                print(f"Trainer spells: {trainer.spells}")
                self.spells_chart = spells_chart
                print(self.spells_chart)
                spell = self.spells_chart[spell_name]
                if spell is None:
                    print(f"{spell_name} is not a valid spell name.")
                    return False
                print(f"Spell type: {spell.spell_type}")
                print(f"Spell Effects: {spell.effects}")
                # Determine the effect of the spell
                if "damage" in spell.effects:
                    print("trainer damage spell")
                    target.trainer_damage(magnitude)
                elif "heal" in spell.effects:
                    target.trainer_heal(magnitude)
                else:
                    print("Invalid spell effect.")
                    return False
            else:
                return [self._apply_spell_to_pokemon(trainer, spell_name, target, spells_chart)]
        else:
            print("This item cannot be used to cast a spell.")
            return False

    def _apply_spell_to_pokemon(self, trainer, spell_name, pokemon, spells_chart):
        
        print(f"_apply_spell_to_pokemon trainer name: {trainer.name}")
        # Use the Spell on the target Pokemon
        print("_apply spell to pokemon target cast spell")
        if spell_name in spells_chart:
            spell = spells_chart[spell_name]
            
            # Print the type of the spell and the type of the target Pokemon
            print(f"Spell type: {spell.spell_type}")
            print(f"Spell Effects: {spell.effects}")
            # Check if the spell's type matches the target Pokemon's type
            return spell.cast(trainer, pokemon)
        else:

            print(f"spells_chart: {spells_chart}")
            print(f"{spell_name} is not a valid spell name._apply_spell_to_pokemon")
            return False

    def update_item_quantity(self, item):
        print(f"Inside update_item_quantity, item: {item}")
        if item is None:
            print("Error: item is None")
            return

        if isinstance(self.items, dict):
            print(f"Decrementing item quantity in dict: {item.name}")
            self.items[item.name][1] -= 1
            if self.items[item.name][1] == 0:
                del self.items[item.name]
        elif isinstance(self.items, list):
            index_to_remove = None
            for i, item_object in enumerate(self.items):
                if item_object.name == item.name:
                    print(f"Decrementing item quantity in list: {item.name}")
                    item_object.quantity -= 1
                    if item_object.quantity <= 0:
                        index_to_remove = i
                    break

            # If the item's quantity reaches 0, remove it from the list
            if index_to_remove is not None:
                self.items.pop(index_to_remove)

    def choose_pokemon(self, item_name=None):
        if len(self.pokemon_list) == 1:
            print(f"{self.name}, you only have one Pokemon, you can't switch.")
            return False

        if self.is_human:
            prompt = f"Which Pokemon would you like to use {item_name} on, {self.name}?" if item_name else f"Which Pokemon would you like to switch to, {self.name}?"
            print(prompt)
            print("0. Go Back")
            for i, pokemon in enumerate(self.pokemon_list):
                # Modified line to include current HP and max HP
                print(f"{i + 1}. {pokemon.name} (HP: {pokemon.current_health}/{pokemon.max_health})")
            while True:
                pokemon_choice = input("Enter the number of the Pokemon: ")
                if pokemon_choice.isdigit() and 0 <= int(pokemon_choice) <= len(self.pokemon_list):
                    if int(pokemon_choice) == 0:
                        return None
                    chosen_pokemon = self.pokemon_list[int(pokemon_choice) - 1]
                    if chosen_pokemon.current_health > 0 or item_name == "Revive" or item_name == "Max Revive":
                        print(f"{self.name} chose {chosen_pokemon.name}!")
                        if item_name is not None:
                            print(f"{self.name} will use {item_name} on {chosen_pokemon.name}!")
                        return chosen_pokemon
                    else:
                        print(f"You can't switch to {chosen_pokemon.name} because it has fainted. Please choose another Pokemon.")
                else:
                    print("Invalid choice. Please try again.")
        else:
            alive_pokemon = [pokemon for pokemon in self.pokemon_list if pokemon.current_health > 0]
            if alive_pokemon:
                chosen_pokemon = random.choice(alive_pokemon)
                print(f"{self.name} chose {chosen_pokemon.name}!")
                return chosen_pokemon
            else:
                return None

    def choose_opponent_pokemon(self):
        """Choose one of the opponent's Pokemon."""
        print("Which Pokemon would you like to target?")
        for i, pokemon in enumerate(self.opponent.pokemon_list, 1):
            print(f"{i}. {pokemon.name} (HP: {pokemon.current_health}/{pokemon.max_health})")
        print("0. Go Back")
        while True:
            try:
                choice = int(input("Enter your choice: "))
                if choice < 0 or choice > len(self.opponent.pokemon_list):
                    print("Invalid choice. Please choose again.")
                else:
                    break
            except ValueError:
                print("Invalid input. Please enter a number.")
        if choice == 0:
            return None
        return self.opponent.pokemon_list[choice - 1]

    def choose_move(self, pokemon, item_use=False):
        if self.is_human:
            if item_use:
                print("Which move would you like to use the item on?")
            else:
                print(f"{self.name}, what should {pokemon.name} do?")
                print("0. Go back")

            for i, move in enumerate(pokemon.moves, 1):
                print(f"{i}. {move.name} - PP: {move.pp}/{move.max_pp}")  # Added PP information
            while True:
                choice = input("> ")
                if choice.isdigit() and 0 <= int(choice) <= len(pokemon.moves):
                    if int(choice) == 0:
                        return None
                    else:
                        move = pokemon.moves[int(choice) - 1]
                        if item_use:
                            print(f"You will use the item on {move.name}!")
                        else:
                            print(f"{pokemon.name} will use {move.name}!")
                            for effect, magnitude in move.effects.items():
                                print(f'The move has the following effect: {effect} with a magnitude of {magnitude}')
                        return move
                else:
                    print("Invalid choice. Please enter a number corresponding to a move or '0' to go back.")
        else:
            # AI logic for computer-controlled trainers
            move = random.choice(pokemon.moves)
            print(f"{self.name}'s {pokemon.name} will use {move.name}!")
            return move

    def battle_wild_pokemon(self, region, sub_region, pokemons, game_state):
        if sub_region is None:
            regional_pokemons = [pokemon for pokemon in pokemons.values() if region in pokemon.region]
        else:
            regional_pokemons = [pokemon for pokemon in pokemons.values() if region in pokemon.region and sub_region in pokemon.sub_region]

        if not regional_pokemons:  # Add this check
            print("No Pokemon found in the specified region and sub-region.")
            return

        rarity_multiplier = 1
        while True:
            # Create a deep copy of the wild_pokemon to make sure it's a separate instance
            wild_pokemon = copy.deepcopy(random.choices(regional_pokemons, weights=[pokemon.rarity * rarity_multiplier for pokemon in regional_pokemons])[0])
            print(f"Battle Wild Pokemon: Current wild pokemon: {wild_pokemon.name}")
            wild_pokemon.level = random.gauss(mu=wild_pokemon.level, sigma=15)
            wild_pokemon.level = max(1, min(100, int(wild_pokemon.level)))
            print(f"A wild {wild_pokemon.name} appeared! It's level {wild_pokemon.level}!")
            wild_trainer = Trainer("Wild Pokemon", [wild_pokemon], is_human=False)
            wild_trainer.active_pokemon = wild_pokemon
            print(f"{self.name} vs a Wild {wild_pokemon.name} Level {wild_pokemon.level}")
            self.start_battle_with_wild_pokemon()

            try:
                battle_result = PygameBattle(game_state, self, wild_trainer, self.moves_dict, self).start()
            except PokemonCaptured:
                print("You have captured the wild Pokemon and ended the battle.")
                return  # Return here to prevent the rest of the method from executing

            self.end_battle_with_wild_pokemon()

            # Insert your item_used check here
            #if self.item_used:
            #    self.use_item_in_battle(wild_pokemon=wild_pokemon)

            if battle_result == "win":
                while True:  # Keep asking until a valid response is given
                    try:
                        continue_battle = continue_battle_prompt_pygame(screen, font)
                        if continue_battle == 1:
                            rarity_multiplier += 0.1
                            wild_pokemon.level += 5
                        else:
                            break
                    except ValueError:
                        print("Invalid input. Please enter 1 for yes or 0 for no.")
                if continue_battle == 1:
                    rarity_multiplier += 0.1
                    wild_pokemon.level += 5
                else:
                    break
            else:
                break

    def add_pokemon(self, pokemon):
        self.pokemon_list.append(pokemon)
        print(f"{self.name} added {pokemon.name} to their Pokemon list!")

    def swap_pokemon(self):
        # This method allows the trainer to swap a Pokemon from their team with a Pokemon from their storage.
        print(f"{self.name}, which Pokemon would you like to swap?")
        print("0. Go back")
        for i, pokemon in enumerate(self.pokemon_list):
            print(f"{i + 1}. {pokemon.name}")
        team_choice = int(input("Choose a Pokemon from your team: ")) - 1
        if team_choice == -1:
            return
        if team_choice < 0 or team_choice >= len(self.pokemon_list):
            print("Invalid choice. Please try again.")
            return

        print(f"{self.name}, which Pokemon would you like to swap with?")
        print("0. Go back")
        for i, pokemon in enumerate(self.storage):
            print(f"{i + 1}. {pokemon.name}")
        storage_choice = int(input("Choose a Pokemon from your storage: ")) - 1
        if storage_choice == -1:
            return
        if storage_choice < 0 or storage_choice >= len(self.storage):
            print("Invalid choice. Please try again.")
            return

        # Swap the Pokemon
        self.pokemon_list[team_choice], self.storage[storage_choice] = self.storage[storage_choice], self.pokemon_list[team_choice]
        print(f"{self.name} swapped {self.pokemon_list[team_choice].name} with {self.storage[storage_choice].name}!")

    def deposit_pokemon(self):
        print("Choose a Pokemon to deposit:")
        for i, pokemon in enumerate(self.pokemon_list, 1):
            print(f"{i}. {pokemon.name}")
        choice = input("Enter the number of the Pokemon: ")
        if choice == '':
            print("Invalid input. Please enter a number.")
            return
        try:
            choice = int(choice) - 1
        except ValueError:
            print("Invalid input. Please enter a number.")
            return
        if 0 <= choice < len(self.pokemon_list):
            deposited_pokemon = self.pokemon_list.pop(choice)
            self.storage.append(deposited_pokemon)
            print(f"{deposited_pokemon.name} has been deposited.")
        else:
            print("Invalid choice. Please try again.")

    def withdraw_pokemon(self):
        if len(self.pokemon_list) >= 6:
            print("Your team is full. You can't withdraw more Pokemon.")
            return
        print("Choose a Pokemon to withdraw:")
        for i, pokemon in enumerate(self.storage, 1):
            print(f"{i}. {pokemon.name}")
        choice = input("Enter the number of the Pokemon: ")
        if choice == '':
            print("Invalid input. Please enter a number.")
            return
        try:
            choice = int(choice) - 1
        except ValueError:
            print("Invalid input. Please enter a number.")
            return
        if 0 <= choice < len(self.storage):
            withdrawn_pokemon = self.storage.pop(choice)
            self.pokemon_list.append(withdrawn_pokemon)
            print(f"{withdrawn_pokemon.name} has been withdrawn.")
        else:
            print("Invalid choice. Please try again.")

    def trainer_heal(self, amount):
        self.current_health = min(self.max_health, self.current_health + amount)
        print(f"{self.name} healed for {amount} health. Current health: {self.current_health}/{self.max_health}")
    
    def trainer_damage(self, amount):
        self.current_health = max(0, self.current_health - amount)
        print(f"{self.name} took {amount} damage. Current health: {self.current_health}/{self.max_health}")

class Battle:
    def __init__(self, trainer1, trainer2, moves_dict, wild_pokemon=None):
        if trainer1 == trainer2:
            raise ValueError("A trainer cannot battle themselves!")
        self.trainer1 = trainer1
        self.trainer2 = trainer2
        self.trainer1.opponent = trainer2  # Add this line
        self.trainer2.opponent = trainer1  # Add this line
        self.wild_pokemon = wild_pokemon  # Add this attribute
        self.last_item_used = None  # Add this line
        self.item_used = False  # Add this line
        self.pokemon_captured = False  # Add this line
        self.moves_dict = moves_dict
        self.exit_game = False
        self.turn = 0

    def start(self):
        print(f"Start: {self.trainer1.name}'s active pokemon: {self.trainer1.current_pokemon.name}")
        print(f"Start: {self.trainer2.name}'s active pokemon: {self.trainer2.current_pokemon.name}")
        try:
            #print(type(self.trainer1))
            #print(type(self.trainer2))
            print(f"{self.trainer1.name} ({'Human' if self.trainer1.is_human else 'AI'}) vs {self.trainer2.name} ({'Human' if self.trainer2.is_human else 'AI'})\n")
            while True:
                for trainer in (self.trainer1, self.trainer2):
                    if self.check_status_effect_in_battle(trainer):
                        continue

                    # Pass wild_pokemon to execute_action_in_battle
                    self.execute_action_in_battle(trainer, self.trainer2.current_pokemon, self.wild_pokemon)

                    if self.pokemon_captured:
                        print("Pokemon captured flag is set.")
                        return "win"
                    if self.item_used:
                        self.item_used = False
                        break

                    if self.check_fainted_pokemon_in_battle(trainer):
                        if trainer == self.trainer1:
                            return "lose"
                        else:
                            return "win"

                    self.print_status()
        except ExitBattle:
            print("Start method completed without capturing a Pokemon.")
            self.exit_game = True
            return "lose"
        except PokemonCaptured:
            print("You have captured the wild Pokemon and ended the battle.")
            return "win"

    def check_status_effect_in_battle(self, trainer):
        if trainer.current_pokemon.check_status_effect():
            print(f"{trainer.current_pokemon.name} is affected by {trainer.current_pokemon.status} and can't move!")
            return True
        return False

    def execute_action_in_battle(self, trainer, opponent_pokemon, wild_pokemon):
        print(f"Execute Action: {trainer.name}'s active pokemon: {trainer.current_pokemon.name}")
        while True:
            if trainer == self.trainer1:
                # Pass wild_pokemon to choose_action
                action, target = trainer.choose_action(wild_pokemon=wild_pokemon, opponent_pokemon=opponent_pokemon)
            else:
                action, target = trainer.auto_choose_action()

            if action == "move":
                # Check if the move has PP
                if target.pp > 0:
                    target.use(trainer.current_pokemon, trainer.opponent.current_pokemon)
                    if trainer.opponent.current_pokemon.current_health <= 0:
                        break
                    else:
                        break
                else:
                    print(f"{target.name} can't be used because it has no PP left!")
                    continue  # Continue the loop instead of breaking it
            elif action == "switch":
                if self.switch_pokemon_in_battle(trainer, target):
                    break
            elif action == "item" and trainer == self.trainer1:
                # If battling a wild Pokemon, pass the wild Pokemon to use_item_in_battle()
                #if action == "item" and trainer == self.trainer1:
                capture_success, captured_pokemon = self.use_item_in_battle(trainer, wild_pokemon)
                if capture_success:
                    self.pokemon_captured = True
                    print("A wild Pokémon has been captured!")
                    return
            elif action == "attack":  # Add this condition
                # Perform the attack action
                trainer.perform_attack_action(trainer.opponent.current_pokemon)  # Use opponent's Pokemon here
                break  # End the trainer's turn after an attack action

            if trainer.item_used:
                trainer.item_used = False
                break

    def switch_pokemon_in_battle(self, trainer, new_pokemon):
        if new_pokemon is not None:
            trainer.current_pokemon = new_pokemon
            print(f"{trainer.name} switched out Pokemon! Go, {new_pokemon.name}!")
            return True
        return False

    def use_item_in_battle(self, trainer, wild_pokemon):
        print(f"Use Item in Battle: Current wild pokemon: {wild_pokemon.name}")
        item, quantity = trainer.choose_item()
        if item is None:
            return "item", None
        if trainer.use_item(item, quantity, wild_pokemon=wild_pokemon):
            self.item_used = True
            return None, None
        else:
            if len(trainer.items) == 0:
                print("You have no items to use. Please choose another action.")
            return None, None

    def check_fainted_pokemon_in_battle(self, trainer):
        if trainer.opponent.current_pokemon.current_health <= 0:
            self.handle_fainted_pokemon(trainer.current_pokemon, trainer.opponent.current_pokemon)

            if all(pokemon.current_health <= 0 for pokemon in trainer.opponent.pokemon_list):
                print(f"{trainer.name} won the battle!")
                self.end_battle(trainer)
                return True
            else:
                print(f"{trainer.opponent.name}, your current pokemon has fainted. Choose a new pokemon.")
                new_pokemon = trainer.opponent.choose_pokemon()
                if new_pokemon is None:
                    # User selected to go back, ask if they want to exit the battle.
                    try:
                        confirm_exit = int(input(f"Would you like to exit battle with {self.wild_pokemon.name}? (1 for yes/0 for no): ").strip())
                    except ValueError:
                        print("Please enter 1 for yes or 0 for no.")
                        # Optionally, you can loop back to re-prompt the user here.
                    else:
                        if confirm_exit == 1:
                            raise ExitBattle
                        elif confirm_exit == 0:
                            # Re-prompt for a Pokemon to switch to.
                            new_pokemon = trainer.opponent.choose_pokemon()
                        else:
                            print("Please enter 1 for yes or 0 for no.")
                            # Optionally, you can loop back to re-prompt the user here.
                # Set the current_pokemon to the chosen Pokemon (new_pokemon) here.
                trainer.opponent.current_pokemon = new_pokemon
        return False

    def handle_fainted_pokemon(self, winning_pokemon, fainted_pokemon):
        """
        Handles what happens when a Pokemon faints.
        """
        # Give experience to the winning Pokemon
        experience_gain = fainted_pokemon.level * 10  # Example calculation
        self.trainer1.current_pokemon.gain_experience(experience_gain, self.trainer1.moves_dict)
        #print(f"\n{fainted_pokemon.name} has fainted and {winning_pokemon.name} gained {experience_gain} experience points.")

    def end_battle(self, winning_trainer):
        #print(f"{winning_trainer.name} won the battle!")
        if winning_trainer == self.trainer1:  # if the player is the winner
            coins_won = int(self.trainer2.coins * 0.1)  # player wins 10% of the opponent's coins
            self.trainer1.coins += coins_won
            self.trainer2.coins -= coins_won
            print(f"{winning_trainer.name} won {coins_won} coins from {self.trainer2.name}!")
        # Assuming the winning trainer's current Pokemon was the one that won the fight
        #winning_trainer.current_pokemon.experience += 50  # Arbitrary experience gain
        #winning_trainer.current_pokemon.level_up(self.moves_dict)  # Check if the Pokémon levels up

    def print_status(self):
        print(f"{self.trainer1.name}'s {self.trainer1.current_pokemon.name} HP: {self.trainer1.current_pokemon.current_health}/{self.trainer1.current_pokemon.max_health}")
        print(f"{self.trainer2.name}'s {self.trainer2.current_pokemon.name} HP: {self.trainer2.current_pokemon.current_health}/{self.trainer2.current_pokemon.max_health}")


def main_menu(game_state):
    print("Main Menu:")
    print("1. Start new game")
    print("2. Continue")
    print("3. Load game")
    print("4. Exit game")
    choice = input("Enter your choice: ")

    if choice == '1':  # Start new game
        pass
    elif choice == '2':  # Continue
        loaded_data = load_last_game(game_state)  # Call load_last_game() instead of load_game()
        if loaded_data is not None:
            game_state = loaded_data  # Update the game state
    elif choice == '3':  # Load game
        loaded_data = load_game(game_state)
        if loaded_data is not None:
            game_state = loaded_data  # Update the game state
            return game_state  # Return the loaded game state
    elif choice == '4':  # Exit game
        return None
    else:
        print("Invalid choice. Please try again.")
        return main_menu(game_state)

    return choice  # Return the choice made by the user

def pre_battle_menu(human_trainer, trainers, pokemons, items, tm_chart, spells_chart, moves, moves_dict):
    game_state = {
        'human_trainer': human_trainer,
        'trainers': trainers,
        'pokemons': pokemons,
        'items': items
    }
    while True:
        print("Pre-Battle Menu:")
        print("1. Choose a trainer to battle")
        print("2. Battle a random trainer")
        print("3. Battle a wild Pokemon")
        print("4. Visit Pokemart")
        print("5. Visit the Pokecenter")
        print("6. Access storage")
        print("7. Save game")
        print("8. Load game")
        print("9. Delete game")
        print("10. Battle trainers by team")
        print("11. Battle trainers by region/sub-region")
        print("12. Start new game")
        print("13. Team Info")
        print("0. Exit game")
        choice = input("Enter your choice: ")
        if choice.isdigit():
            choice = int(choice)
            if choice == 1:
                opponent_trainer = choose_trainer_to_battle(human_trainer, trainers, moves)
                if opponent_trainer is not None:
                    return opponent_trainer  # Return the trainer, not the Battle
            elif choice == 2:
                opponent_trainer = battle_random_trainer(human_trainer, trainers, moves)
                if opponent_trainer is not None:
                    return opponent_trainer  # Return the trainer, not the Battle
            elif choice == 3:
                battle_wild_pokemon_menu(human_trainer, pokemons)
            elif choice == 4:
                visit_pokemart(human_trainer, items)
            elif choice == 5:
                visit_pokecenter(human_trainer)
            elif choice == 6:
                access_storage(human_trainer, trainers, pokemons, items)
            elif choice == 7:
                save_game(human_trainer, trainers, pokemons, items)
            elif choice == 8:
                loaded_data = load_game(game_state)
                if loaded_data is not None:
                    game_state = loaded_data  # Update the game state
            elif choice == 9:
                delete_saved_game()
            elif choice == 10:
                return battle_trainers_by_team(human_trainer, trainers, moves_dict)
            elif choice == 11:
                return battle_trainers_by_region(human_trainer, trainers, moves_dict)
            elif choice == 12:
                human_trainer = start_new_game(trainers, pokemons, items, tm_chart, spells_chart, moves)
                print(f"Human trainer after starting new game: {human_trainer}")  # Add this line
            elif choice == 13:
                team_info_menu(human_trainer, trainers, pokemons, items)
            elif choice == 0:
                exit()
        print("Invalid input. Please enter a number.")
    return human_trainer  # Return the updated human_trainer

def battle_trainers_by_team(human_trainer, trainers, moves_dict):
    team_names = list(set([trainer.team for trainer in trainers if trainer.name != human_trainer.name]))
    print("Available teams:")
    for i, team_name in enumerate(team_names, 1):
        print(f"{i}. {team_name}")
    team_choice = input("Enter the number of the team you want to battle: ")
    if team_choice.isdigit():
        team_choice = int(team_choice) - 1
        if 0 <= team_choice < len(team_names):
            team_trainers = [trainer for trainer in trainers if trainer.team == team_names[team_choice] and trainer.name != human_trainer.name]
            if team_trainers:
                for trainer in team_trainers:
                    battle = Battle(human_trainer, trainer, moves_dict)
                    winner = battle.start()
                    if battle.exit_game:
                        break
                    if winner == human_trainer:
                        human_trainer.coins += 1000  # Award coins for winning
                        human_trainer.choose_pokemon()  # Prompt to switch Pokemon
    else:
        print("No trainers found in the specified team.")
    return None

def get_sub_regions_by_region(region):
    locations_df = pd.read_csv('locations2.csv')
    return locations_df[locations_df['region'] == region]['sub_region'].tolist()

def battle_trainers_by_region(human_trainer, trainers, moves_dict):
    region_names = list(set([trainer.region for trainer in trainers if trainer.name != human_trainer.name]))
    print("Available regions:")
    for i, region_name in enumerate(region_names, 1):
        print(f"{i}. {region_name}")

    region_choice = input("Enter the number of the region you want to battle in: ")
    if region_choice.isdigit():
        region_choice = int(region_choice) - 1
        if 0 <= region_choice < len(region_names):
            selected_region = region_names[region_choice]
            sub_regions = get_sub_regions_by_region(selected_region)
            print(f"Available sub-regions in {selected_region}:")
            for i, sub_region in enumerate(sub_regions, 1):
                print(f"{i}. {sub_region}")

            sub_region_choice = input("Enter the number of the sub-region you want to battle in: ")
            if sub_region_choice.isdigit():
                sub_region_choice = int(sub_region_choice) - 1
                if 0 <= sub_region_choice < len(sub_regions):
                    selected_sub_region = sub_regions[sub_region_choice]
                    region_trainers = [trainer for trainer in trainers if trainer.region == selected_region and trainer.sub_region == selected_sub_region and trainer.name != human_trainer.name]
                    
                    if region_trainers:
                        for trainer in region_trainers:
                            battle = Battle(human_trainer, trainer, moves_dict)
                            winner = battle.start()
                            if battle.exit_game:
                                break
                            if winner == human_trainer:
                                human_trainer.coins += 1000  # Award coins for winning
                                human_trainer.choose_pokemon()  # Prompt to switch Pokemon
                    else:
                        print("No trainers found in the selected sub-region.")
                else:
                    print("Invalid sub-region choice.")
            else:
                print("Invalid input for sub-region choice.")
        else:
            print("Invalid region choice.")
    else:
        print("Invalid input for region choice.")

    return None

def choose_trainer_to_battle(human_trainer, trainers, moves_dict):
    possible_opponents = [trainer for trainer in trainers if trainer != human_trainer]
    for i, trainer in enumerate(possible_opponents):
        print(f"{i + 1}. {trainer.name}")
    trainer_choice = input("Choose a trainer to battle: ")
    if trainer_choice.isdigit():
        trainer_choice = int(trainer_choice) - 1
        if trainer_choice in range(len(possible_opponents)):
            return possible_opponents[trainer_choice]  # Return the trainer, not the Battle
    print("Invalid choice. Please try again.")
    return None

def battle_random_trainer(human_trainer, trainers, moves_dict):
    possible_opponents = [trainer for trainer in trainers if trainer != human_trainer]
    if possible_opponents:
        return random.choice(possible_opponents)  # Return the trainer, not the Battle
    else:
        print("No other trainers available to battle.")
        return None

def choose_region(regions):
    while True:
        print("Choose a region:")
        print("0. Go back")
        for i, region in enumerate(regions, 1):
            print(f"{i}. {region}")
        region_choice = input("Enter the number of the region: ")
        if region_choice.isdigit():
            region_choice = int(region_choice) - 1
            if region_choice == -1:
                return None
            elif region_choice in range(len(regions)):
                return regions[region_choice]
        print("Invalid input. Please enter a number.")

def choose_sub_region(sub_regions):
    while True:
        print("Choose a sub-region:")
        print("0. Go back")
        print("1. Entire region")
        for i, sub_region in enumerate(sub_regions, 2):
            print(f"{i}. {sub_region}")
        sub_region_choice = input("Enter the number of the sub-region: ")
        if sub_region_choice.isdigit():
            sub_region_choice = int(sub_region_choice) - 1
            if sub_region_choice == -1:
                return None
            elif sub_region_choice == 0:
                return ""  # Return an empty string for "Entire region"
            elif 1 <= sub_region_choice < len(sub_regions) + 1:
                return sub_regions[sub_region_choice - 1]
        print("Invalid input. Please enter a number.")

def continue_battle_prompt():
    while True:  # Keep asking until a valid response is given
        try:
            continue_battle = int(input("Would you like to continue battling wild Pokemon? (1 for yes/0 for no): "))
            if continue_battle not in [0, 1]:
                raise ValueError  # Raise a ValueError if the input is not 0 or 1
            break  # Exit the loop if the input is valid
        except ValueError:
            print("Invalid input. Please enter 1 for yes or 0 for no.")
    return continue_battle

def battle_wild_pokemon_menu(human_trainer, pokemons, game_state):
    regions = list(set([region for pokemon in pokemons.values() for region in pokemon.region if region and str(region).lower() != 'nan']))
    chosen_region = choose_region(regions)
    if chosen_region is None:
        return
    sub_regions = list(set([sub_region for pokemon in pokemons.values() for sub_region in pokemon.sub_region if chosen_region in pokemon.region and sub_region and str(sub_region).lower() != 'nan']))
    chosen_sub_region = choose_sub_region(sub_regions)
    if chosen_sub_region is None:
        return
    if chosen_sub_region == "":
        chosen_sub_region = None
    while True:
        try:
            print("Starting wild battle")
            human_trainer.battle_wild_pokemon(chosen_region, chosen_sub_region, pokemons, game_state)
            continue_battle = continue_battle_prompt()
            if continue_battle == 0:
                break
        except ExitBattle:
            print("Battle ended prematurely")

#Pokemart code
def get_numeric_input(prompt):
    while True:
        user_input = input(prompt)
        if user_input.isdigit():
            return int(user_input)
        print("Invalid input. Please enter a number.")

def get_choice_from_list(item_list):
    while True:
        user_input = get_numeric_input("Enter your choice: ") - 1
        if 0 <= user_input < len(item_list):
            return user_input
        print("Invalid choice. Please try again.")

def buy_item(trainer, items):
    print("\nItems available for purchase:")
    for i, item_name in enumerate(items, 1):
        item = items[item_name]
        print(f"{i}. {item.name} - {item.price} coins")

    item_choice = get_choice_from_list(items)
    item_name = list(items.keys())[item_choice]
    item = items[item_name]
    quantity = get_numeric_input("Enter the quantity you want to buy: ")

    total_price = item.price * quantity
    if trainer.coins >= total_price:
        trainer.coins -= total_price
        for trainer_item in trainer.items:
            if trainer_item.name == item_name:
                trainer_item.quantity += quantity
                break
        else:
            trainer.items.append(Item(item.name, item.description, item.effect, item.price, item.evolution, quantity))
        print(f"You bought {quantity} {item.name}! You now have {trainer.coins} coins.")
    else:
        print("You don't have enough coins to buy this quantity.")

def sell_item(trainer):
    if trainer.items:
        print("\nItems available for sale:")
        for i, item in enumerate(trainer.items, 1):
            print(f"{i}. {item.name} - {item.price // 2} coins")

        item_choice = get_choice_from_list(trainer.items)
        item = trainer.items[item_choice]
        if item.quantity > 0:
            item.quantity -= 1
            if item.quantity == 0:
                trainer.items.remove(item)
            trainer.coins += item.price // 2
            print(f"You sold {item.name}! You now have {trainer.coins} coins.")
        else:
            print("You don't have that item.")
    else:
        print("You don't have any items to sell.")

def visit_pokemart(trainer, items):
    while True:
        print(f"\nWelcome to the Pokemart! You currently have {trainer.coins} coins.")
        print("1. Buy items")
        print("2. Sell items")
        print("3. Exit Pokemart")

        choice = get_numeric_input("Enter your choice: ")

        if choice == 1:
            buy_item(trainer, items)
        elif choice == 2:
            sell_item(trainer)
        elif choice == 3:
            break
        else:
            print("Invalid choice. Please try again.")

def visit_pokecenter(trainer):
    print(f"{trainer.name} visited the Pokecenter.")
    for pokemon in trainer.pokemon_list:
        pokemon.current_health = pokemon.max_health
        for move in pokemon.moves:
            move.pp = move.max_pp
    print("All your Pokémon have been healed to full health.")

def access_storage(human_trainer, trainers, pokemons, items):
    while True:
        print("0. Go back")
        print("1. Deposit Pokemon")
        print("2. Withdraw Pokemon")
        print("3. Swap Pokemon")
        storage_choice = input("Choose an action: ")
        if storage_choice == '1':
            human_trainer.deposit_pokemon()
        elif storage_choice == '2':
            human_trainer.withdraw_pokemon()
        elif storage_choice == '3':
            human_trainer.swap_pokemon()
        elif storage_choice == '0':
            break
        else:
            print("Invalid choice. Please try again.")

def start_new_game(trainers, pokemons, items, tm_chart, spells_chart, moves):
    # Check if there are any other human trainers and change them to AI
    for trainer in trainers:
        if trainer.is_human:
            trainer.is_human = False

    # Prompt the user for their trainer name, region, and sub-region
    trainer_name = input("Enter your trainer name: ")
    trainer_region = input("Enter your region: ")
    trainer_sub_region = input("Enter your sub-region: ")

    # Create a new trainer with 100000 coins
    trainer_coins = 100000
    trainer_items = items  # Assuming items is a dictionary
    trainer_pokemons = []
    team = None  # You can set this to a specific team if needed
    spells = None  # You can set this to a specific set of spells if needed
    mana = 100  # You can set this to a specific amount of mana if needed
    max_health = 20

    # Choose starting Pokemon
    print("Choose your starting Pokemon:")
    pokemon_list = list(pokemons.values())  # Create a list of Pokemon

    # Select 50 random Pokemon and create deep copies with levels from a bell curve distribution centered at 30
    if len(pokemon_list) > 50:
        pokemon_list = random.sample(pokemon_list, 50)
    leveled_pokemon_list = []
    for pokemon in pokemon_list:
        pokemon_copy = copy.deepcopy(pokemon)

        # Generate a level using a normal distribution centered around 30
        level = max(1, min(100, int(np.random.normal(loc=30, scale=7))))
        pokemon_copy.level = level

        # Adjust stats based on level and randomness
        pokemon_copy.max_health = int(pokemon.max_health * (level / 30) * random.uniform(0.8, 1.2))
        pokemon_copy.attack = int(pokemon.attack * (level / 30) * random.uniform(0.8, 1.2))
        pokemon_copy.defense = int(pokemon.defense * (level / 30) * random.uniform(0.8, 1.2))
        pokemon_copy.speed = int(pokemon.speed * (level / 30) * random.uniform(0.8, 1.2))
        pokemon_copy.current_health = pokemon_copy.max_health  # Set current health to max_health

        # Adjust price based on level
        pokemon_copy.price *= level

        # Get the last 4 moves that the Pokemon can learn at its current level
        pokemon_copy.moves = PokemonFactory.get_moves_at_level(pokemon_copy.moves_to_learn, pokemon_copy.level, moves)

        leveled_pokemon_list.append(pokemon_copy)

    for i, pokemon in enumerate(leveled_pokemon_list, 1):  # Iterate over the list
        print(f"{i}. {pokemon.name} (Level {pokemon.level}) - {pokemon.price} coins")

    for _ in range(6):
        while True:
            pokemon_choice = input("Enter the number of the Pokemon you want to add to your team: ")
            if pokemon_choice.isdigit():
                pokemon_choice = int(pokemon_choice) - 1
                if 0 <= pokemon_choice < len(leveled_pokemon_list):  # Check if the choice is within the range of the list
                    chosen_pokemon = leveled_pokemon_list[pokemon_choice]  # Use the choice to index the list
                    if trainer_coins >= chosen_pokemon.price:
                        trainer_coins -= chosen_pokemon.price
                        trainer_pokemons.append(chosen_pokemon)
                        print(f"You bought {chosen_pokemon.name} (Level {chosen_pokemon.level})! You now have {trainer_coins} coins.")
                        break
                    else:
                        print("You don't have enough coins to buy this Pokemon.")
                else:
                    print("Invalid choice. Please try again.")
            else:
                print("Invalid input. Please enter a number.")

    # Create the new trainer
    new_trainer = Trainer(trainer_name, trainer_pokemons, is_human=True, items=trainer_items, coins=trainer_coins, team=team, region=trainer_region, sub_region=trainer_sub_region, spells=spells, mana=mana, max_health=max_health, tm_chart=tm_chart, spells_chart=spells_chart, moves_dict=moves)

    # Add the new trainer to the list of trainers
    trainers.append(new_trainer)

    # Set the first pokemon as the current pokemon if the list is not empty
    if new_trainer.pokemon_list:
        new_trainer.current_pokemon = new_trainer.pokemon_list[0]

    return {
        'trainers': trainers,
        'human_trainer': new_trainer,
        'pokemons': pokemons,  # The list of all pokemons doesn't change
        'items': items,  # The list of all items doesn't change
        'tm_chart': tm_chart,  # The TM chart doesn't change
        'spells_chart': spells_chart,
        'moves': moves  # The list of all moves doesn't change
    }

def is_data_valid_for_save(data):
    return isinstance(data, tuple) and len(data) == 4

def save_game(human_trainer, trainers, pokemons, items):
    save_data = (human_trainer, trainers, pokemons, items)
    if not is_data_valid_for_save(save_data):
        print("Error: Game data is in an invalid format and cannot be saved.")
        return
    
    save_name = input("Enter a name for your save: ")
    save_file_path = f'{save_name}.pkl'
    
    # Check if the existing save file (if it exists) is valid before overwriting
    if os.path.exists(save_file_path):
        try:
            with open(save_file_path, 'rb') as f:
                existing_data = pickle.load(f)
            if not is_data_valid_for_save(existing_data):
                print(f"Warning: Existing save file '{save_name}.pkl' seems corrupted. Proceed with caution if you choose to overwrite.")
        except pickle.UnpicklingError:
            print(f"Warning: Existing save file '{save_name}.pkl' seems corrupted. Proceed with caution if you choose to overwrite.")
    
    # Actual saving process
    with open(save_file_path, 'wb') as f:
        pickle.dump(save_data, f)
    print("Game saved.")

def delete_saved_game():
    save_files = get_save_files()
    if not save_files:
        print("No saved games found.")
        return

    print_save_files(save_files)

    save_file_choice = get_user_choice(len(save_files))
    if save_file_choice == -1:
        return
    os.remove(save_files[save_file_choice])
    print(f"Deleted saved game {save_files[save_file_choice]}")

def load_game(game_state):
    saves = get_save_files()
    if not saves:
        print("No saved games found.")
        return game_state

    print_save_files(saves)

    while True:
        save_choice = get_user_choice(len(saves))
        if save_choice == -1:
            print("Invalid choice. Please try again.")
            continue
        try:
            game_state = load_game_from_file(saves[save_choice], game_state)
            print("Game loaded.")
            return game_state
        except pickle.UnpicklingError:
            print("Load Game Saved game is corrupted.")
    return game_state

def load_last_game(game_state):
    saves = get_save_files()
    if not saves:
        print("No saved games found.")
        return game_state
    latest_save = max(saves, key=os.path.getmtime)
    try:
        game_state = load_game_from_file(latest_save, game_state)
        print("Game loaded.")
        return game_state
    except pickle.UnpicklingError:
        print("Saved game is corrupted.")
    return game_state

def load_game_from_file(filename, game_state):
    try:
        with open(filename, 'rb') as f:
            loaded_data = pickle.load(f)
    except pickle.UnpicklingError:
        raise ValueError("Load Game - Unpickling Error: Saved game is corrupted.")
    
    # Debug: print the type and shape (if it's a tuple) of the loaded data
    print(f"Type of loaded data: {type(loaded_data)}")
    if isinstance(loaded_data, tuple):
        print(f"Length of loaded tuple: {len(loaded_data)}")
    
    if isinstance(loaded_data, tuple) and len(loaded_data) == 5:
        game_state['human_trainer'], game_state['trainers'], game_state['pokemons'], game_state['items'], additional_data = loaded_data
        # If you need to use additional_data somewhere, you can add it to the game_state or handle it appropriately.
        return game_state
    else:
        raise ValueError("Loaded data does not match expected format.")

def get_user_choice(max_value, back_option=False):
    while True:
        user_choice = input("Enter the number of the save to load: ")
        if user_choice.isdigit():
            user_choice = int(user_choice)
            if back_option and user_choice == 0:
                return -1
            elif 1 <= user_choice <= max_value:
                return user_choice - 1
        print("Invalid choice. Please try again.")

def get_save_files():
    return glob.glob('*.pkl')

def print_save_files(save_files):
    print("Choose a saved game to delete:")
    print("0. Go back")
    for i, save_file in enumerate(save_files, 1):
        print(f"{i}. {save_file}")

def team_info_menu(human_trainer, trainers, pokemons, items):
    while True:
        print("\nTeam Info Menu:")
        print(f"Trainer Name: {human_trainer.name}")
        print(f"Region: {human_trainer.region}")
        print(f"Sub-region: {human_trainer.sub_region}")
        print(f"Coins: {human_trainer.coins}")
        print(f"Max HP: {human_trainer.max_health}")
        print("1. View/Edit Current Pokemon Team")
        print("2. Access Pokemon Storage")
        print("3. View/Use Item Inventory")
        print("0. Go Back")
        choice = input("Enter your choice: ")
        if choice.isdigit():
            choice = int(choice)
            if choice == 1:
                # Call a function to view/edit the current Pokemon team
                view_edit_pokemon_team(human_trainer)
            elif choice == 2:
                # Call a function to access Pokemon storage
                access_storage(human_trainer, trainers, pokemons, items)
            elif choice == 3:
                # Call a function to view/use item inventory
                view_use_item_inventory(human_trainer)
            elif choice == 0:
                return
        print("Invalid input. Please enter a number.")

def view_edit_pokemon_team(human_trainer):
    chosen_pokemon = human_trainer.choose_pokemon()
    if chosen_pokemon:
        print_pokemon_info(chosen_pokemon)
    else:
        print("No Pokemon selected.")

def view_use_item_inventory(trainer):
    # Let the trainer choose an item
    item, quantity = trainer.choose_item()
    
    # If an item was chosen
    if item:
        # Display the trainer's current Pokemon team
        print("Choose a Pokemon to use the item on:")
        for i, pokemon in enumerate(trainer.pokemon_list):
            print(f"{i + 1}. {pokemon.name}")
        
        # Let the trainer choose a Pokemon
        choice = int(input("Enter your choice: ")) - 1
        if 0 <= choice < len(trainer.pokemon_list):
            selected_pokemon = trainer.pokemon_list[choice]
            
            # Use the item on the selected Pokemon
            trainer.use_item(selected_pokemon, item, quantity)
        else:
            print("Invalid choice. Please enter a number corresponding to a Pokemon.")

def print_pokemon_info(pokemon):
    print(f"Name: {pokemon.name}")
    print(f"Type: {pokemon.ptype}")
    print(f"Level: {pokemon.level}")
    print(f"Current HP: {pokemon.current_health}")
    print(f"Max HP: {pokemon.max_health}")
    print(f"Attack: {pokemon.attack}")
    print(f"Defense: {pokemon.defense}")
    print(f"Speed: {pokemon.speed}")
    print(f"Experience: {pokemon.experience}")
    print(f"Experience needed for next level: {pokemon.level_up_experience - pokemon.experience}")
    print(f"Moves: {', '.join([move.name for move in pokemon.moves])}")
    print("\n")

#initialize game refactored:

def load_items_from_csv(file_path, moves):
    items = {}
    with open(file_path, 'r') as f:
        reader = csv.reader(f)
        next(reader)  # Skip the header row
        for row in reader:
            item_name = row[0]
            item_type = row[1]
            print(f"Item Type: {item_type}")
            item_description = row[2]
            item_effects = row[3].split('/')  # Split the effects and their magnitudes
            effect_dict = {}
            for effect in item_effects:
                try:
                    effect_name, effect_magnitude = effect.split(':')
                    print(f"Effect: {effect}, Effect Name: {effect_name}, Effect Magnitude: {effect_magnitude}")
                    effect_dict[effect_name] = float(effect_magnitude)  # Convert the magnitude to float
                except ValueError:
                    print(f"Error parsing effects for item: {item_name}")
                    print(f"Effect string: {effect}")
                    effect_dict[effect] = 1  # Default value if parsing fails
            print(f"Effect: {effect}, Effect Name: {effect_name}, Effect Magnitude: {effect_magnitude}")
            print(f"Loaded item {item_name} with effects {effect_dict}")  # Add this line
            item_target = row[4]
            item_price = int(row[5])
            item_rarity = int(row[6])  # Assuming rarity is an integer
            # Handle additional columns here
            # ...
            if "TM" in item_name or "HM" in item_name:
                # Extract the move name from the item name
                move_name = ' '.join(item_name.split(' ')[1:]).replace('(', '').replace(')', '')
                move = moves[move_name]  # Get the Move instance from the moves dictionary
                item = TMHM(item_name, move)
            else:
                item = Item(item_name, item_type, item_description, effect_dict,item_target, item_price, item_rarity)

            items[item_name] = item
    return items

def load_spells_from_csv(file_path):
    spells = {}
    with open(file_path, 'r') as f:
        reader = csv.reader(f)
        next(reader)  # Skip the header row
        for row in reader:
            name = row[0]
            spell_type = row[1]
            mana_cost = int(row[2])
            price = int(row[3])
            duration = row[4]
            effects = row[5].split('/')
            effect_dict = {}
            for effect in effects:
                effect_name, effect_magnitude = effect.split(':')
                effect_dict[effect_name] = float(effect_magnitude)
            effect_type = row[6]
            power = int(row[7])
            level = int(row[8])
            details = row[9]
            spell = Spell(name, spell_type, mana_cost, price, duration, effect_dict, effect_type, power, level, details)
            spells[name] = spell
    return spells

def load_tm_chart(file_path, moves):
    tm_chart = {}
    with open(file_path, 'r') as f:
        reader = csv.reader(f)
        next(reader)  # Skip the header row
        for row in reader:
            if len(row) < 2:  # Skip rows with fewer than 2 values
                continue
            tm_number, move_name = row
            move = moves[move_name]  # Get the Move instance from the moves dictionary
            tm_chart[tm_number] = move
    return tm_chart

def load_spells_chart(file_path, spells):
    spells_chart = {}
    with open(file_path, 'r') as f:
        reader = csv.reader(f)
        next(reader)  # Skip the header row
        for row in reader:
            if len(row) < 2:  # Skip rows with fewer than 2 values
                continue
            spell_name, _ = row[0], row[1:]  # Assuming the spell name is the first value in the row
            spell = spells[spell_name]  # Get the Spell instance from the spells dictionary
            spells_chart[spell_name] = spell
    return spells_chart

def load_moves_from_csv(filename):
    df = pd.read_csv(filename)
    moves = {}
    for _, row in df.iterrows():
        effects = parse_effect(row['Effect'])
        move = Move(row['Move Name'], row['Type'], row['Power'], row['Accuracy'], row['PP'], level=1, effects=effects)
        moves[move.name] = move
    return moves

def load_pokemons_from_csv(filename, moves):
    df = pd.read_csv(filename)
    pokemons = {}
    for _, row in df.iterrows():
        attributes = parse_pokemon_attributes(row, moves)
        pokemon = Pokemon(attributes)
        pokemons[pokemon.name] = pokemon
    return pokemons

def load_trainers_from_csv(filename, pokemons, items, moves, spells, tm_chart):
    df = pd.read_csv(filename)
    trainers = []
    for _, row in df.iterrows():
        trainer_pokemons = parse_trainer_pokemon_data(row, pokemons, moves)
        trainer_items = parse_trainer_items(row, items)
        trainer = Trainer(row['Trainer Name'], trainer_pokemons, is_human=row['Trainer Type'] == 'Human', items=trainer_items, coins=row['Coins'], team=row['Team'], region=row['Region'], sub_region=row['Sub Region'], spells=[spells[s] for s in row['Spells'].split('/') if pd.notna(row['Spells'])], mana=int(row['Mana']), max_health=int(row['Max_Health']), tm_chart=tm_chart, moves_dict=moves)
        trainers.append(trainer)
    return trainers

def load_evolution_stones_from_pokemons_df(pokemons_dict):
    evolution_stones = {}
    for pokemon in pokemons_dict.values():
        evolution_item = getattr(pokemon, 'Evolution_Item', None)
        if evolution_item:
            evolution_stones.setdefault(evolution_item, []).append(pokemon.name)
    return evolution_stones

def parse_effect(effect_str):
    effects = effect_str.split('/')
    return {effect.split(':')[0]: int(effect.split(':')[1]) for effect in effects}

def parse_moves_to_learn(moves_str):
    moves = moves_str.split('/')
    return {move.split(':')[0]: int(move.split(':')[1]) for move in moves if ':' in move}

def parse_pokemon_attributes(row, moves):
    moves_to_learn = parse_moves_to_learn(row['Moves'])
    pokemon_moves = PokemonFactory.get_moves_at_level(moves_to_learn, row['Level'], moves)
    return {
        'Name': row['Name'],
        'Index': row['Index'],
        'Level': row['Level'],
        'Type': row['Type'].split('/') if pd.notna(row['Type']) else [],
        'Max_Health': row['Max_Health'],
        'Attack': row['Attack'],
        'Defense': row['Defense'],
        'Speed': row['Speed'],
        'Moves': pokemon_moves,
        'Moves_to_Learn': moves_to_learn,
        'Evolved_Form': row['Evolved_Form'],
        'Evolution_Level': row['Evolution_Level'],
        'Evolution_Item': row['Evolution_Item'],
        'Abilities': row['Abilities'].split('/') if pd.notna(row['Abilities']) else [],
        'Held_Item': row['Held_Item'],
        'Region': row['Region'].split('/') if pd.notna(row['Region']) else [],
        'Sub_Region': row['Sub_Region'].split('/') if pd.notna(row['Sub_Region']) else [],
        'Mana_Cost': row['Mana_Cost'],
        'Rarity': row['Rarity'],
        'Price': row['Price'],
        'Description': row['Description']
    }

def parse_trainer_pokemon_data(row, pokemons, moves):
    trainer_pokemons = []
    for pokemon_entry in row['Trainer Pokemons'].split('/'):
        pokemon_name, pokemon_level = pokemon_entry.split(':')
        base_data = {
            'Name': pokemons[pokemon_name].name,
            'Index': pokemons[pokemon_name].index,
            'Type': pokemons[pokemon_name].ptype,
            'Max_Health': pokemons[pokemon_name].max_health,
            'Attack': pokemons[pokemon_name].attack,
            'Defense': pokemons[pokemon_name].defense,
            'Speed': pokemons[pokemon_name].speed,
            'Moves_to_Learn': pokemons[pokemon_name].moves_to_learn,
            'Evolved_Form': pokemons[pokemon_name].evolved_form,
            'Evolution_Level': pokemons[pokemon_name].evolution_level,
            'Evolution_Item': pokemons[pokemon_name].evolution_item,
            'Abilities': pokemons[pokemon_name].abilities,
            'Held_Item': pokemons[pokemon_name].held_item,
            'Region': pokemons[pokemon_name].region,
            'Sub_Region': pokemons[pokemon_name].sub_region,
            'Mana_Cost': pokemons[pokemon_name].mana_cost,
            'Rarity': pokemons[pokemon_name].rarity,
            'Price': pokemons[pokemon_name].price,
            'Description': pokemons[pokemon_name].description
        }

        base_data['Moves'] = PokemonFactory.get_moves_at_level(base_data['Moves_to_Learn'], int(pokemon_level), moves)
        pokemon = PokemonFactory.create_pokemon(base_data, int(pokemon_level), moves)
        trainer_pokemons.append(pokemon)
    return trainer_pokemons

def parse_trainer_items(row, items):
    trainer_items = {}
    if pd.notna(row['Items']):
        for item_entry in row['Items'].split('/'):
            item_name, quantity = item_entry.split(':')
            trainer_items[item_name] = [items[item_name], int(quantity)]
    return trainer_items

def pre_battle_setup(human_trainer, trainers, pokemons, items, tm_chart, spells_chart, moves):
    """Sets up pre-battle conditions."""
    for pokemon in human_trainer.pokemon_list:
        pokemon.heal(pokemon.max_health)  # heal to max hp

    return pre_battle_menu(human_trainer, trainers, pokemons, items, tm_chart, spells_chart, moves, moves)

def battle_setup(human_trainer, opponent, moves):
    """Initiates and starts a battle."""
    print("battle_setup")
    battle = Battle(human_trainer, opponent, moves)
    battle.start()

def game_over_conditions(human_trainer):
    """Checks conditions for game over."""
    if all([pokemon.is_fainted() for pokemon in human_trainer.pokemon_list]):
        print("All your pokemons have fainted. Game Over.")
        return True
    return False

def initialize_game():
    # Load data
    print("loading moves...")
    moves = load_moves_from_csv('moves5.csv')
    print("moves loaded")
    print("loading items...")
    items = load_items_from_csv('items4.csv', moves)
    print("items loaded")
    print("loading spells...")
    spells = load_spells_from_csv('spells.csv')
    print("spells loaded")
    print("loading tm_chart...")
    tm_chart = load_tm_chart('tm.csv', moves)
    print("tm_chart loaded")
    print("loading spells_chart...")
    spells_chart = load_spells_chart('spells.csv', spells)
    print("spells_chart loaded")
    print("loading pokemon...")
    pokemons = load_pokemons_from_csv('pokemon7.csv', moves)
    print("pokemon loaded")
    print("loading trainers...")
    trainers = load_trainers_from_csv('trainers2.csv', pokemons, items, moves, spells, tm_chart)
    print("trainers loaded")
    # Since you're referring to `pokemons_df` in the next line but it's not defined anywhere in the given code, 
    # I assume it should be the DataFrame returned by `load_pokemons_from_csv`. 
    # Therefore, replace `pokemons_df` with `pokemons` in the next line:
    evolution_stones = load_evolution_stones_from_pokemons_df(pokemons)

    human_trainer = next((t for t in trainers if t.is_human), None)
    game_state = {
        'trainers': trainers,
        'human_trainer': human_trainer,
        'pokemons': pokemons,
        'items': items,
        'tm_chart': tm_chart,
        'spells_chart': spells_chart,
        'moves': moves,
        'current_sub_region': 'test2'  # Setting the initial current subregion
    }

    return(game_state)

def main_menu_loop(game_state):
    while True:
        choice = main_menu(game_state)  # Display the main menu and get the user's choice

        if choice == '1':  # Start new game
            game_state = start_new_game(game_state)
        elif choice == '2':  # Continue (load last game)
            game_state = load_last_game(game_state)
        elif choice == '3':  # Load game
            game_state = load_game(game_state)
        elif choice == '4':  # Exit game
            break

        trainers = game_state['trainers']
        human_trainer = game_state['human_trainer']

        if not human_trainer:
            print("No human trainer found. Exiting game.")
            return

        # Start a battle
        while len(game_state['trainers']) > 1:  # while there are still trainers left
            opponent = pre_battle_setup(human_trainer, game_state['trainers'], game_state['pokemons'], game_state['items'], game_state['tm_chart'], game_state['spells_chart'], game_state['moves'])
            if not opponent:
                continue

            opponent = copy.deepcopy(opponent)
            battle_setup(human_trainer, opponent, game_state['moves'])

            if game_over_conditions(human_trainer):
                break

        end_game_message(len(game_state['trainers']))

def end_game_message(remaining_trainers):
    if remaining_trainers:
        print("Game Over.")
    else:
        print("Congratulations! You've defeated all the trainers.")

"""def initialize_game():

    # Read moves from moves.csv
    moves_df = pd.read_csv('moves5.csv')

    # Create a dictionary to store all moves
    moves = {}
    spells = {}

    for _, row in moves_df.iterrows():
        # Split the effects and their magnitudes
        effects = row['Effect'].split('/')
        effect_dict = {}
        for effect in effects:
            effect_name, effect_magnitude = effect.split(':')
            effect_dict[effect_name] = int(effect_magnitude)
        move = Move(row['Move Name'], row['Type'], row['Power'], row['Accuracy'], row['PP'], level=1, effects=effect_dict)
        moves[move.name] = move


    #print(moves)  # Add this line

    # Read pokemons from pokemon.csv
    pokemons_df = pd.read_csv('pokemon6.csv')

    # Create a dictionary to store all pokemons
    pokemons = {}

    for _, row in pokemons_df.iterrows():
        # Parse the moves and the levels at which they are learned
        moves_to_learn = {}
        for move in row['Moves'].split('/'):
            if ':' in move:
                move_name, move_level = move.split(':')
                moves_to_learn[move_name] = int(move_level)
            else:
                print(f"Warning: Move '{move}' in Pokemon '{row['Name']}' does not have an associated level.")
        # Get the last 4 moves that the Pokemon can learn at its current level
        pokemon_moves = PokemonFactory.get_moves_at_level(moves_to_learn, row['Level'], moves)

        pokemon_attributes = {
            'Name': row['Name'],
            'Level': row['Level'],
            'Type': row['Type'].split('/') if pd.notna(row['Type']) else [],
            'Max_Health': row['Max_Health'],
            'Attack': row['Attack'],
            'Defense': row['Defense'],
            'Speed': row['Speed'],
            'Moves': pokemon_moves,
            'Moves_to_Learn': moves_to_learn,
            'Evolved_Form': row['Evolved_Form'],
            'Evolution_Level': row['Evolution_Level'],
            'Evolution_Item': row['Evolution_Item'],
            'Abilities': row['Abilities'].split('/') if pd.notna(row['Abilities']) else [],
            'Held_Item': row['Held_Item'],
            'Region': row['Region'].split('/') if pd.notna(row['Region']) else [],
            'Sub_Region': row['Sub_Region'].split('/') if pd.notna(row['Sub_Region']) else [],
            'Mana_Cost': row['Mana_Cost'],
            'Rarity': row['Rarity'],
            'Price': row['Price'],
            'Description': row['Description']
        }
        pokemon = Pokemon(pokemon_attributes)
        pokemons[pokemon.name] = pokemon
        #print(f"{pokemon.name} Moves_to_Learn: {pokemon.moves_to_learn}")

    # Create a dictionary to map each evolution stone to the Pokémon that can evolve using it
    evolution_stones = {}
    for _, row in pokemons_df.iterrows():
        pokemon_name = row['Name']
        evolution_item = row['Evolution_Item']
        if evolution_item:  # If the Pokémon has an evolution item
            if evolution_item not in evolution_stones:
                evolution_stones[evolution_item] = []
            evolution_stones[evolution_item].append(pokemon_name)

    # Load items from items.csv
    items = load_items_from_csv('items4.csv', moves)  # Pass the moves dictionary to the function
    # Load spells from spells.csv
    spells = load_spells_from_csv('spells.csv')
    # Load the TM chart
    tm_chart = load_tm_chart('tm.csv', moves)
    print(f"tm_chart: {tm_chart}")
    spells_chart = load_spells_chart('spells.csv', spells)
    print(f"spells_chart: {spells_chart}")

    # Read trainers from trainers.csv
    trainers_df = pd.read_csv('trainers2.csv')

    trainers = []
    human_trainer = None
    for _, row in trainers_df.iterrows():
        trainer_pokemons_entries = row['Trainer Pokemons'].split('/')
        trainer_pokemons = []
        for pokemon_entry in trainer_pokemons_entries:
            pokemon_name, pokemon_level = pokemon_entry.split(':')
            base_data = {
                'Name': pokemons[pokemon_name].name,
                'Type': pokemons[pokemon_name].ptype,
                'Max_Health': pokemons[pokemon_name].max_health,
                'Attack': pokemons[pokemon_name].attack,
                'Defense': pokemons[pokemon_name].defense,
                'Speed': pokemons[pokemon_name].speed,
                'Moves_to_Learn': pokemons[pokemon_name].moves_to_learn,  # Add this line
                'Evolved_Form': pokemons[pokemon_name].evolved_form,  # Add this line
                'Evolution_Level': pokemons[pokemon_name].evolution_level,
                'Evolution_Item': pokemons[pokemon_name].evolution_item,
                'Abilities': pokemons[pokemon_name].abilities,
                'Held_Item': pokemons[pokemon_name].held_item,
                'Region': pokemons[pokemon_name].region,
                'Sub_Region': pokemons[pokemon_name].sub_region,
                'Mana_Cost': pokemons[pokemon_name].mana_cost,
                'Rarity': pokemons[pokemon_name].rarity,
                'Price': pokemons[pokemon_name].price,
                'Description': pokemons[pokemon_name].description
            }
            # Get the last 4 moves that the Pokemon can learn at its current level
            #print(f"{pokemons[pokemon_name].name} Moves_to_Learn: {pokemons[pokemon_name].moves_to_learn}")
            pokemon_moves = PokemonFactory.get_moves_at_level(base_data['Moves_to_Learn'], int(pokemon_level), moves)
            base_data['Moves'] = pokemon_moves  # Assign the moves to the Pokemon
            # create a unique pokemon instance for each trainer's pokemon
            pokemon = PokemonFactory.create_pokemon(base_data, int(pokemon_level), moves)
            trainer_pokemons.append(pokemon)


        trainer_items = {}
        print(f"Items: {items}")  # Debug print
        if pd.notna(row['Items']):
            for item_entry in row['Items'].split('/'):
                item_name, quantity = item_entry.split(':')
                item = items[item_name]
                print(f"Processing item: {item_name}")  # Debug print
                print(f"Processing item type: {item.item_type}")
                print(f"Processing description: {item.description}")
                print(f"Processing effect: {item.effect}")
                print(f"Processing target: {item.target}")
                print(f"Processing price: {item.price}")
                #print(f"Processing rarity: {item.rarity}")
                if isinstance(item.effect, dict):
                    trainer_items[item_name] = [item, int(quantity)]  # Store the Item object and the quantity in a list
                else:
                    print(f"Error: {item_name}'s effect is not a dictionary, but {type(item.effect)} with value {item.effect}")  # Debug print
                    raise TypeError(f"Expected 'item.effect' to be a dictionary, but got {type(item.effect)} instead.")
        trainer_coins = row['Coins']  # Read the coins from the CSV file

        team = row['Team']
        region = row['Region']
        sub_region = row['Sub Region']
        
        # Parse the spells
        trainer_spells = []
        if pd.notna(row['Spells']):
            for spell_name in row['Spells'].split('/'):
                spell = spells[spell_name]
                trainer_spells.append(spell)

        mana = int(row['Mana'])
        max_health = int(row['Max_Health'])

        trainer = Trainer(row['Trainer Name'], trainer_pokemons, is_human=row['Trainer Type'] == 'Human', items=trainer_items, coins=trainer_coins, team=team, region=region, sub_region=sub_region, spells=trainer_spells, mana=mana, max_health=max_health, tm_chart=tm_chart, moves_dict=moves)
        trainer.current_pokemon = trainer.pokemon_list[0]
        print(f"Set current_pokemon for {trainer.name} as {trainer.current_pokemon.name}")

        # Print trainer's name and type
        trainer_type = "Human" if trainer.is_human else "AI"
        print(f"Trainer Name: {trainer.name}, Trainer Type: {trainer_type}")

        trainers.append(trainer)
        if trainer.is_human:
            human_trainer = trainer

    # Create a dictionary to store the game state
    game_state = {
        'trainers': trainers,
        'human_trainer': human_trainer,
        'pokemons': pokemons,
        'items': items,
        'tm_chart': tm_chart,
        'spells_chart': spells_chart,
        'moves': moves
    }

    #app = QtWidgets.QApplication(sys.argv)
    #window = PokemonBattleGUI(trainers, pokemons, items, tm_chart, spells_chart, moves)
    # Display the main menu and start the game
    while True:
        choice = main_menu(game_state)  # Display the main menu and get the user's choice

        if choice == '1':  # Start new game
            new_game_state = start_new_game(game_state['trainers'], game_state['pokemons'], game_state['items'], game_state['tm_chart'], game_state['spells_chart'], game_state['moves'])
            print(f"New game state: {new_game_state}")  # Add this line
            game_state['trainers'] = new_game_state['trainers']
            game_state['human_trainer'] = new_game_state['human_trainer']
        elif choice == '2':  # Continue (load last game)
            game_state = load_last_game(game_state)
        elif choice == '3':  # Load game
            game_state = load_game(game_state)
        elif choice == '4':  # Exit game
            break

        trainers = game_state['trainers']  # Update the list of trainers
        human_trainer = game_state['human_trainer']
        print(f"Human trainer: {human_trainer}")  # Add this line

        if human_trainer is None:
            print("No human trainer found. Exiting game.")
            return

        # Start a battle
        while len(game_state['trainers']) > 1:  # while there are still trainers left
            # heal all of the human trainer's pokemons before the battle
            for pokemon in human_trainer.pokemon_list:
                pokemon.heal(pokemon.max_health)  # heal to max hp

            opponent_trainer = pre_battle_menu(human_trainer, game_state['trainers'], game_state['pokemons'], game_state['items'], game_state['tm_chart'], game_state['spells_chart'], game_state['moves'], game_state['moves']) # choose an opponent from the pre-battle menu
            if opponent_trainer is None:
                continue

            # Create a new instance of the opponent
            opponent = copy.deepcopy(opponent_trainer)

            battle = Battle(human_trainer, opponent, game_state['moves'])  # Pass the moves dictionary to the Battle class
            battle.start()  # start the battle

            # if player's all pokemons are fainted after the battle, game over
            if all([pokemon.is_fainted() for pokemon in human_trainer.pokemon_list]):
                print("All your pokemons have fainted. Game Over.")
                break

        if game_state['trainers']:  # if there are still trainers left
            print("Game Over.")
        else:  # no trainers left, you've defeated all the trainers
            print("Congratulations! You've defeated all the trainers.")"""

#PYGAME CODE

# Adjust this global variable for scroll speed if necessary
SCROLL_SPEED = 5
# Updated Button class with valid color tuples
class Button:
    def __init__(self, x, y, width, height, text=None, color=(0, 128, 128), 
                 highlighted_color=(255, 255, 255), function=None, params=None):  # Changed highlighted_color to white
        self.image = pygame.Surface((width, height), pygame.SRCALPHA) 
        self.pos = (x, y)
        self.rect = self.image.get_rect()
        self.rect.topleft = self.pos
        self.text = text
        self.color = color
        self.highlighted_color = highlighted_color
        self.function = function
        self.params = params
        self.highlighted = False
        self.clicked = False
        self.active = True
        
        self.button_font_path = "pixeled.ttf"
        self.cooldown = 500
        self.last_clicked = 0

        if self.text:
            if isinstance(self.text, pygame.Surface):
                self.image.blit(self.text, (0, 0))
            else:
                font = pygame.font.Font(self.button_font_path, 72)
                text_image = font.render(self.text, True, (65, 255, 255))
                text_rect = text_image.get_rect(center=self.rect.center)
                self.image.blit(text_image, text_rect)

    def update(self, mouse_pos, mouse_up, offset=0, keyboard_navigation=False):
        global last_global_click
        self.rect.y -= offset
        current_time = pygame.time.get_ticks()

        if keyboard_navigation:
            # Redraw the button based on whether it's highlighted
            self.redraw_button(self.highlighted_color if self.highlighted else self.color)
        else:
            if self.rect.collidepoint(mouse_pos):
                self.highlighted = True
                if mouse_up and current_time - self.last_clicked > self.cooldown:
                    self.clicked = True
                    self.last_clicked = current_time
                    if self.function:
                        self.function(*self.params if self.params else [])
            else:
                self.highlighted = False
                self.redraw_button(self.color)  # Reset to normal appearance

        self.rect.y += offset

    def is_over(self, pos):
        """Check if the mouse is over the button"""
        if self.rect.collidepoint(pos):
            return True
        return False

    def redraw_button(self, fill_color):
        # Clear the button's surface
        self.image.fill((0, 0, 0, 0))  # Clear with transparent color

        # Redraw the button with the new color
        pygame.draw.rect(self.image, fill_color, self.image.get_rect(), border_radius=20)

        # Pixelate the button for the desired effect
        scaled_down = pygame.transform.scale(self.image, (self.rect.width // 4, self.rect.height // 4))
        pixelated = pygame.transform.scale(scaled_down, (self.rect.width, self.rect.height))
        self.image.blit(pixelated, (0, 0))

        # Redraw the text after pixelation effect
        if self.text:
            if isinstance(self.text, pygame.Surface):
                self.image.blit(self.text, (0, 0))
            else:
                font = pygame.font.Font(self.button_font_path, 40)
                text_image = font.render(self.text, True, (255, 255, 255))
                text_rect = text_image.get_rect(center=(self.rect.width // 2, (self.rect.height // 2) - 6))
                self.image.blit(text_image, text_rect)

    def draw(self, screen, offset=0):
        if self.active:
            temp_image = pygame.Surface((self.rect.width, self.rect.height), pygame.SRCALPHA)

            # If highlighted, fill the button with 100% opacity
            if self.highlighted:
                fill_color = (*self.color, 255)
            else:
                fill_color = (*self.color, 192)

            pygame.draw.rect(temp_image, fill_color, temp_image.get_rect(), border_radius=20)
            
            # Pixelate the button for the desired effect
            scaled_down = pygame.transform.scale(temp_image, (self.rect.width // 4, self.rect.height // 4))
            pixelated = pygame.transform.scale(scaled_down, (self.rect.width, self.rect.height))
            
            screen.blit(pixelated, (self.rect.topleft[0], self.rect.topleft[1] + offset))

            # Draw the text after pixelation effect
            if self.text:
                if isinstance(self.text, pygame.Surface):
                    screen.blit(self.text, (self.rect.topleft[0], self.rect.topleft[1] + offset))
                else:
                    font = pygame.font.Font(self.button_font_path, 40)
                    text_image = font.render(self.text, True, (255, 255, 255))
                    text_rect = text_image.get_rect(center=(self.rect.width // 2, (self.rect.height // 2) - 6))  # Adjusted y position by +5
                    screen.blit(text_image, (self.rect.topleft[0] + text_rect.x, self.rect.topleft[1] + offset + text_rect.y))

            
            if self.highlighted:
                # Create a surface for the border and draw the border on it
                border_surf = pygame.Surface((self.rect.width, self.rect.height), pygame.SRCALPHA)
                pygame.draw.rect(border_surf, self.highlighted_color, border_surf.get_rect(), 10, border_radius=20)

                # Pixelate the border
                scaled_down_border = pygame.transform.scale(border_surf, (self.rect.width // 4, self.rect.height // 4))
                pixelated_border = pygame.transform.scale(scaled_down_border, (self.rect.width, self.rect.height))

                screen.blit(pixelated_border, (self.rect.topleft[0], self.rect.topleft[1] + offset))

class PokemonButton(Button):
    def __init__(self, x, y, width, height, pokemon, game_state, color=(0, 128, 128), highlighted_color=(255, 255, 255), function=None, params=None):
        super().__init__(x, y, width, height, pokemon.name.upper(), color, highlighted_color, function, params)
        self.pokemon = pokemon
        self.pokemon_image = pygame.image.load(get_pokemon_image_path(pokemon.name, game_state['pokemons']))  # Load the Pokémon image using game_state
        self.pokemon_image = pygame.transform.scale(self.pokemon_image, (50, 50))  # Adjust the size as needed
        self.highlighted = False  # Add this line

    def draw(self, screen, offset=0):
        # First, call the parent class's draw method to handle the button background and highlighting
        super().draw(screen, offset)

        # Then draw the additional PokemonButton-specific elements (like the Pokemon image)
        image_x = self.rect.x + 5
        image_y = self.rect.y + 5 + offset
        screen.blit(self.pokemon_image, (image_x, image_y))

        # Draw white border around Pokémon image
        border_rect = pygame.Rect(image_x - 2, image_y - 2, self.pokemon_image.get_width() + 4, self.pokemon_image.get_height() + 4)
        pygame.draw.rect(screen, (255, 255, 255), border_rect, 2)

        # Text configuration
        name_font = pygame.font.Font(None, 20)  # Smaller size for the Pokémon name
        hp_font = pygame.font.Font(None, 16)  # Font for the HP text

        # Draw Pokémon name and level
        name_text = f"Lv{self.pokemon.level} {self.pokemon.name}"
        name_text_render = name_font.render(name_text, True, (255, 255, 255))
        text_x = self.rect.x + 60
        text_y = self.rect.y + 20 + offset  # Adjusted y-coordinate for name
        screen.blit(name_text_render, (text_x, text_y))

        # Draw HP bar and text with adjusted y-coordinate
        hp_bar_x = text_x  # Align HP bar with the name
        hp_bar_y = text_y  # Below the name
        hp_bar_width = 100
        hp_bar_height = 10

        # Add a safety check to prevent division by zero
        if self.pokemon.max_health > 0:
            hp_percentage = self.pokemon.current_health / self.pokemon.max_health
        else:
            hp_percentage = 0

        hp_bar_color = (255, 0, 0) if hp_percentage < 0.2 else (0, 255, 0)
        hp_bar_rect = pygame.Rect(hp_bar_x, hp_bar_y, hp_bar_width * hp_percentage, hp_bar_height)
        pygame.draw.rect(screen, hp_bar_color, hp_bar_rect)

        # Draw HP text aligned with the HP bar
        hp_text = f"{self.pokemon.current_health} / {self.pokemon.max_health}"
        hp_text_render = hp_font.render(hp_text, True, (255, 255, 255))
        screen.blit(hp_text_render, (hp_bar_x, hp_bar_y + hp_bar_height + 5))  # Below the HP bar

class InputBox:
    def __init__(self, x, y, w, h, font, text=''):
        self.rect = pygame.Rect(x, y, w, h)
        self.color_inactive = pygame.Color('lightskyblue3')
        self.color_active = pygame.Color('dodgerblue2')
        self.color = self.color_inactive
        self.text = text
        self.font = font
        self.txt_surface = font.render(text, True, self.color)
        self.active = False

    def set_active(self, active):
        self.active = active
        self.color = self.color_active if self.active else self.color_inactive

    def handle_event(self, event):
        if event.type == pygame.MOUSEBUTTONDOWN:
            if self.rect.collidepoint(event.pos):
                self.active = not self.active
            else:
                self.active = False
            self.color = self.color_active if self.active else self.color_inactive
        if event.type == pygame.KEYDOWN:
            if self.active:
                if event.key == pygame.K_BACKSPACE:
                    self.text = self.text[:-1]
                else:
                    self.text += event.unicode
                self.txt_surface = self.font.render(self.text, True, (255, 255, 255))  # Changed color to black for visibility

    def draw(self, screen):
        pygame.draw.rect(screen, self.color, self.rect, 2)
        screen.blit(self.txt_surface, (self.rect.x + 5, self.rect.y + 5))
        pygame.draw.line(screen, self.color, (self.rect.x + 10 + self.txt_surface.get_width(), self.rect.y + 10), (self.rect.x + 10 + self.txt_surface.get_width(), self.rect.y + self.rect.h - 10))

    def get_text(self):
        return self.text

class Scrollbar:
    def __init__(self, x, y, width, height, handle_height, total_content_height):
        self.x = x
        self.y = y
        self.width = width
        self.height = height
        self.handle_height = min(height, handle_height)
        self.total_content_height = total_content_height
        self.handle_y = y
        self.is_hovered = False

    def draw(self, screen, mouse_pos):
        # Color of the scrollbar handle
        handle_color = (0, 128, 128)  # Color of the buttons
        border_color = (255, 255, 255)  # White color for the border

        # Draw the scrollbar background with 50% opacity
        background_surface = pygame.Surface((self.width, self.height), pygame.SRCALPHA)
        background_surface.fill((200, 200, 200, 128))  # 50% opacity
        screen.blit(background_surface, (self.x, self.y))

        # Adjust transparency for the scrollbar handle
        if self.is_over_handle(mouse_pos) or self.is_hovered:
            alpha = 255  # Opaque when hovered or dragged
            handle_surface = pygame.Surface((self.width, self.handle_height), pygame.SRCALPHA)
            handle_surface.fill((*handle_color, alpha))
            pygame.draw.rect(handle_surface, border_color, handle_surface.get_rect(), 2)  # Adding border
            screen.blit(handle_surface, (self.x, self.handle_y))
        else:
            alpha = 128  # Semi-transparent when not hovered
            handle_surface = pygame.Surface((self.width, self.handle_height), pygame.SRCALPHA)
            handle_surface.fill((*handle_color, alpha))
            screen.blit(handle_surface, (self.x, self.handle_y))

    def move_handle(self, movement):
        # Move the handle within the scrollbar bounds
        self.handle_y = max(self.y, min(self.y + self.height - self.handle_height, self.handle_y + movement))

    def is_over_handle(self, mouse_pos):
        # Check if the mouse is over the scrollbar handle
        return self.x <= mouse_pos[0] <= self.x + self.width and \
               self.handle_y <= mouse_pos[1] <= self.handle_y + self.handle_height

    def get_scroll_percentage(self):
        # Calculate the percentage of how much the content should be scrolled
        return (self.handle_y - self.y) / (self.height - self.handle_height)
    
    def set_handle_position(self, percentage):
        """Set the handle position based on the provided percentage."""
        self.handle_y = self.y + percentage * (self.height - self.handle_height)








class ConfirmationWindow:
    def __init__(self, x, y, width, height, label):
        self.rect = pygame.Rect(x, y, width, height)
        self.label = label
        self.button = Button(x + 50, y + height - 100, 200, 75, text="OK", function=self.close_window)
        self.visible = False
        self.font_path = "pixeled.ttf"  # Path to the Pixeled font

    def draw(self, screen):
        if not self.visible:
            return

        # Draw the window with rounded corners
        pygame.draw.rect(screen, (0, 128, 128), self.rect, border_radius=15)  # Teal background with rounded corners
        pygame.draw.rect(screen, (255, 255, 255), self.rect, 5, border_radius=15)  # White border

        # Draw the label using the Pixeled font
        font = pygame.font.Font(self.font_path, 20)  # Adjust font size as needed
        lines = self.label.split('\n')  # Split the label into lines
        line_height = font.size("Tg")[1]
        start_y = self.rect.centery - (line_height * len(lines) // 2)
        for i, line in enumerate(lines):
            text = font.render(line, True, (255, 255, 255))
            text_rect = text.get_rect(center=(self.rect.centerx, start_y + i * line_height))
            screen.blit(text, text_rect)

        # Draw the button
        self.button.draw(screen)

    def update(self, mouse_pos, mouse_up, keys_pressed):
        if not self.visible:
            return

        self.button.update(mouse_pos, mouse_up)

        # Adjust the condition to check if the mouse is up or RETURN key is pressed
        if self.button.clicked or (mouse_up and keys_pressed[pygame.K_RETURN]):
            print("Closing confirmation window")
            self.close_window()

    def open_window(self, label):
        self.label = label
        self.visible = True

    def close_window(self):
        self.visible = False







class Character:
    def __init__(self, sprite_sheet_path, sprite_size, num_columns, num_rows):
        print(f"Loading character sprite sheet: {sprite_sheet_path}")  # Debugging print
        try:
            self.sprite_sheet = pygame.image.load(sprite_sheet_path)
        except Exception as e:
            print(f"Error loading character sprite sheet: {e}")
            raise
        self.sprite_size = sprite_size
        self.num_columns = num_columns
        self.num_rows = num_rows
        self.animations = self.load_animations()
        self.current_animation = 'idle'
        self.frame_index = 0
        self.position = [400, 300]  # Starting position
        self.rect = pygame.Rect(self.position[0], self.position[1], sprite_size[0], sprite_size[1])  # Initialize the collision rectangle

    def check_for_wild_pokemon_encounter(self, tall_grass_area):
        # Define the chance of encountering a wild Pokémon (e.g., 10% chance)
        encounter_chance = 0.150
        if self.rect.colliderect(tall_grass_area) and random.random() < encounter_chance:
            return True
        return False

    def load_animations(self):
        sprite_sheet_width, sprite_sheet_height = self.sprite_sheet.get_size()
        expected_width = self.sprite_size[0] * self.num_columns
        expected_height = self.sprite_size[1] * self.num_rows

        if sprite_sheet_width < expected_width or sprite_sheet_height < expected_height:
            raise ValueError(f"Sprite sheet is smaller than expected: {sprite_sheet_width}x{sprite_sheet_height}, expected at least {expected_width}x{expected_height}")

        animations = {}
        for row in range(self.num_rows):
            animation_frames = []
            for col in range(self.num_columns):
                frame = self.sprite_sheet.subsurface(pygame.Rect(col * self.sprite_size[0], row * self.sprite_size[1], self.sprite_size[0], self.sprite_size[1]))
                animation_frames.append(frame)
            animations[self.get_animation_name(row)] = animation_frames

        # Flip the 'walk_right' frames for 'walk_left'
        animations['walk_left'] = [pygame.transform.flip(frame, True, False) for frame in animations['walk_right']]

        return animations

    def get_animation_name(self, row):
        animation_names = ['idle', 'walk_right', 'walk_up', 'walk_down', 'run_right', 'run_up', 'attack_down', 'attack_right', 'attack_up', 'crouch']
        return animation_names[row]

    def update(self, keys, collision_rects, dt, tall_grass_area, joystick=None):
        base_speed = 60  # Base speed in pixels per second

        # Determine movement from keyboard
        movement_x = keys[pygame.K_RIGHT] - keys[pygame.K_LEFT]
        movement_y = keys[pygame.K_DOWN] - keys[pygame.K_UP]

        # Determine movement from joystick
        if joystick:
            # Analog stick input
            joystick_x_axis = joystick.get_axis(0)
            joystick_y_axis = joystick.get_axis(1)

            # D-pad input
            # Note: get_hat() returns (-1, 0, or 1) for each axis
            hat_x_axis, hat_y_axis = joystick.get_hat(0)

            # Override keyboard input if joystick input is detected
            # Note: hat_y_axis is inverted (-1 is up, 1 is down)
            movement_x = joystick_x_axis or hat_x_axis or movement_x
            movement_y = joystick_y_axis or -hat_y_axis or movement_y


        # Calculate the amount of movement in x and y direction based on the input and speed
        movement_x = int(round(base_speed * dt * movement_x))
        movement_y = int(round(base_speed * dt * movement_y))

        # Temporary new position that the character will move to
        new_position = [self.position[0] + movement_x, self.position[1] + movement_y]

        # Modify the collider size to be half of the original size
        collider_width = int(self.sprite_size[0] * 0.5)
        collider_height = int(self.sprite_size[1] * 0.5)

        # Adjust the position to keep the collider centered around the character
        collider_x = int(new_position[0] + (self.sprite_size[0] - collider_width) / 2)
        collider_y = int(new_position[1] + (self.sprite_size[1] - collider_height))

        # Create a new rectangle for collision detection at the new position with reduced size
        new_rect = pygame.Rect(collider_x, collider_y, collider_width, collider_height)

        # Collision detection
        if not any(new_rect.colliderect(rect) for rect in collision_rects):
            self.position = new_position  # Update position only if no collision detected
            self.rect.topleft = self.position  # Update the collision rectangle's position

        # Inside the update method, right after calculating new_rect
        # print(f"Character new position: {new_position}, Collider: {new_rect}")

        # Inside the collision detection loop
        for rect in collision_rects:
            if new_rect.colliderect(rect):
                print(f"Collision detected with {rect}")

        # Determine the current animation based on the movement
        if movement_x > 0:
            self.current_animation = 'walk_right'
        elif movement_x < 0:
            self.current_animation = 'walk_left'
        elif movement_y > 0:
            self.current_animation = 'walk_down'
        elif movement_y < 0:
            self.current_animation = 'walk_up'
        else:
            self.current_animation = 'idle'

        # Update the animation frame index
        self.frame_index = (self.frame_index + 1) % len(self.animations[self.current_animation])

    def draw(self, screen):
        frame = self.animations[self.current_animation][self.frame_index]
        screen.blit(frame, self.position)

class NPC:
    def __init__(self, sprite_sheet_path, position, object_bounds, size=(24, 24), speed=1, animation_speed=10, trainer_name=None):
        self.sprite_sheet = pygame.image.load(sprite_sheet_path)
        self.trainer_name = trainer_name  # New attribute for the trainer's name
        self.rect = pygame.Rect(position[0], position[1], size[0], size[1])
        self.object_bounds = object_bounds
        self.speed = speed
        self.direction = 1  # 1 for right, -1 for left
        self.current_frame = 0
        self.animation_speed = animation_speed  # New attribute to control animation speed
        self.frame_counter = 0  # Counter to track when to update the animation frame

    def update(self, player_rect):
        # Stop moving if the player is in front of the NPC
        if self.rect.colliderect(player_rect):
            return  # NPC stops moving if colliding with the player
        
        # Update position
        self.rect.x += self.speed * self.direction

        # Change direction at object boundaries
        if self.rect.left < self.object_bounds.left or self.rect.right > self.object_bounds.right:
            self.direction *= -1

        # Increment the frame counter
        self.frame_counter += 2
        # Update the animation frame only if the frame counter has reached the animation speed threshold
        if self.frame_counter >= self.animation_speed:
            self.current_frame = (self.current_frame + 1) % 4  # Assuming 4 frames per row
            self.frame_counter = 0  # Reset the frame counter

    def draw(self, screen):
        row = 2 if self.direction == 1 else 1  # Row for left or right walking
        frame_rect = (self.current_frame * 24, row * 24, 24, 24)
        frame_image = self.sprite_sheet.subsurface(frame_rect)
        screen.blit(frame_image, self.rect.topleft)

class PygameBattle(Battle):
    
    BASE_HEIGHT = 500
    MOVE_BUTTON_HEIGHT = 50
    MOVE_BUTTON_GAP = 10
    MAX_MOVES = 4  # Assuming a Pokémon can have a maximum of 4 moves
    
    def __init__(self, game_state, trainer1, trainer2, moves_dict, human_trainer):
        super().__init__(trainer1, trainer2, moves_dict)  # Pass the trainers and moves_dict to the parent class's __init__ method
        self.game_state = game_state
        self.scroll_offset = 0
        self.scrollbar_height = 100  # Adjust this as needed
        self.scrollbar_y = 0  # This will be updated based on scrolling
        self.show_scrollbar = False  # New flag
        self.current_trainer = self.trainer1  # Start with player's turn
        self.human_trainer  = human_trainer
        self.item_selected = False
        self.selected_item = None
        self.selected_pokemon = None
        self.selected_trainer = None
        self.selected_move = None
        self.selected_pokemon_team = None
        self.wild_pokemon_target = None

        

        self.font_path = "pixeled.ttf"
        
        print(f"battling wild pokemon: {self.trainer1.battling_wild_pokemon}")
        if self.trainer2.name == 'Wild Pokemon':
            self.wild_pokemon_target = self.trainer2.current_pokemon

        print(f"current wild pokemon target: {self.wild_pokemon_target}")

        self.spells_chart = game_state['spells_chart']

        # Update the trainer's items
        self.trainer1.items = human_trainer.items  # Assuming human_trainer has the updated items

        self.item_targets = {
            'choose_own_pokemon': partial(self.choose_pokemon_pygame),
            'choose_opp_pokemon': partial(self.choose_opponent_pokemon_pygame),
            'opp_trainer': self.trainer2,
            'human_trainer': self,  # Assuming 'self' is the human trainer
            'all_own_pokemon': self.trainer1.pokemon_list,  # All Pokémon belonging to the human trainer
            'all_opp_pokemon': self.trainer2.pokemon_list,  # All Pokémon belonging to the opponent trainer
        }


        self.button_height = 100
        self.button_width = 400
        self.button_a_xpos = 10
        self.button_a_ypos = 680
        self.button_b_xpos = 436
        self.button_b_ypos = 680
        self.button_c_xpos = 863
        self.button_c_ypos = 680
        self.button_d_xpos = 10
        self.button_d_ypos = 800
        self.button_e_xpos = 436
        self.button_e_ypos = 800
        self.button_f_xpos = 863
        self.button_f_ypos = 800

        # Load resources (background and GIFs)
        self.bg_image, self.gif_images, self.gif_images_middle, self.gif_images_top = self.load_resources()

        # Initialize frame counters for GIF animations
        self.current_frame_original = 0
        self.current_frame_middle = len(self.gif_images) // 3
        self.current_frame_top = 2 * len(self.gif_images) // 3

        # Add new attributes for controlling the GIF frame update rate
        self.frame_update_rate = 2  # Number of updates before the GIF frame changes
        self.frame_counter = 0  # Counter to track updates

        
        # Print the current trainer's items for debugging
        print(f"{self.trainer1.name}'s Items: {self.trainer1.items}")

        pygame.init()
        
        # Calculate the height dynamically
        #window_height = self.BASE_HEIGHT + (self.MOVE_BUTTON_HEIGHT + self.MOVE_BUTTON_GAP) * self.MAX_MOVES
        #self.screen = pygame.display.set_mode((800, window_height))

        self.screen = pygame.display.set_mode((1280, 920), pygame.DOUBLEBUF)
        
        pygame.display.set_caption("Pokémon Battle")
        self.font = pygame.font.Font(font_path, 24)
        self.clock = pygame.time.Clock()
        
        # Define the action buttons
        self.buttons = [
            Button(self.button_a_xpos, self.button_a_ypos, self.button_width, self.button_height, "MOVE", function=self.choose_move_pygame),
            Button(self.button_b_xpos, self.button_b_ypos, self.button_width, self.button_height, "SWITCH", function=self.choose_switch_pygame),
            Button(self.button_c_xpos, self.button_c_ypos, self.button_width, self.button_height, "ITEM", function=self.choose_item_pygame),
            Button(self.button_d_xpos, self.button_d_ypos, self.button_width, self.button_height, "ATTACK", function=self.choose_attack_pygame),
            Button(self.button_e_xpos, self.button_e_ypos, self.button_width, self.button_height, "EXIT", function=self.exit_battle)  # New exit button
        ]
        
        print(self.trainer1.pokemon_list)
        print(self.trainer1.current_pokemon)
        #print(self.trainer2.pokemon_list)
        #print(self.trainer2.current_pokemon)
        # Load the images for the Pokémon
        self.trainer1_pokemon_image = pygame.image.load(self.get_pokemon_image_path(self.trainer1.current_pokemon.name))
        self.trainer2_pokemon_image = pygame.image.load(self.get_pokemon_image_path(self.trainer2.current_pokemon.name))

    def get_pokemon_image_path(self, pokemon_name):
        """Return the path to the image for the given Pokémon."""
        pokemons = list(self.game_state["pokemons"].keys())  # Get list of Pokémon names
        #print(pokemons)

        pokemon_details = self.game_state["pokemons"].get(pokemon_name)
        if not pokemon_details:
            raise ValueError(f"No Pokemon found with the name {pokemon_name}")

        # Instantiate the Pokémon object (assuming you have a Pokemon class)
        # This is a basic example, you might need to adjust the arguments based on the Pokemon class' __init__ method
        #pokemon_object = Pokemon(name=pokemon_name, index=)
        print(pokemon_details.index)
        # Find the index based on the position in the list
        try:
            pokemon_index = pokemon_details.index
            print(pokemon_index)
            formatted_index = f"{pokemon_index:04}"  # Zero-pad the index to ensure it's 4 digits
            print(formatted_index)
        except ValueError:
            raise ValueError(f"No Pokemon found with the name {pokemon_name}")
                
        #return os.path.join("F:\\Scripts\\PokePyMain-main\\pokemon_pics", f"{formatted_index}{pokemon_name}.png")
        #return os.path.join("C:\\Users\matth\\OneDrive\\PokePy\\PokePyMain-main\\pokemon_pics", f"{formatted_index}{pokemon_name}.png")
        #return os.path.join("C:\\Users\\Tusa\\OneDrive\\PokePy\\PokePyMain-main\\pokemon_pics", f"{formatted_index}{pokemon_name}.png")
    
        return os.path.join("pokemon_pics", f"{formatted_index}{pokemon_name}.png")

    """def display_pokemon_image(self, trainer, x, y):
        # Display the Pokémon image
        if trainer == self.trainer1:
            self.screen.blit(self.trainer1_pokemon_image, (x, y - 100))  # Adjust y-position as needed
        else:
            self.screen.blit(self.trainer2_pokemon_image, (x, y - 100))  # Adjust y-position as needed

        # Display Pokémon name and health
        text = self.font.render(f"{trainer.name} - {trainer.current_pokemon.name}", True, (0, 0, 0))
        hp_text = self.font.render(f"HP: {trainer.current_pokemon.current_health}/{trainer.current_pokemon.max_health}", True, (0, 255, 0))
        self.screen.blit(text, (x, y))
        self.screen.blit(hp_text, (x, y + 30))"""

    def choose_move_pygame(self):
        # Clear current buttons
        self.buttons.clear()
        
        # Define fonts
        font = pygame.font.Font(font_path, 24)  # For move name
        small_font = pygame.font.Font(font_path, 12)  # For PP

        btn_width, btn_height = self.button_width, self.button_height
        spacing = 25
        initial_x, initial_y = 20, 660

        # Determine x and y for the buttons
        for i, move in enumerate(self.trainer1.current_pokemon.moves):
            row = i // 3
            col = i % 3
            x = initial_x + (btn_width + spacing) * col
            y = initial_y + (btn_height + spacing) * row

            move_name_surface = font.render(move.name.upper(), True, (255, 255, 255))
            pp_surface = small_font.render(f"(PP: {move.pp}/{move.max_pp})", True, (255, 255, 255))
            
            combined_height = move_name_surface.get_height() + pp_surface.get_height()
            combined_text = pygame.Surface((btn_width, combined_height), pygame.SRCALPHA, 32)
            combined_text.blit(move_name_surface, (0, 0))
            combined_text.blit(pp_surface, (0, move_name_surface.get_height()))

            btn = Button(x, y, btn_width, btn_height + combined_height - font.get_height(), combined_text, function=self.execute_move, params=[move])
            self.buttons.append(btn)

        # Add a 'Go Back' button
        x_back = initial_x + (btn_width + spacing) * 2  # Adjust if needed
        y_back = initial_y + (btn_height + spacing) * -1 # Adjust if needed
        back_btn = Button(x_back, y_back, btn_width, btn_height, "BACK", function=self.back_to_main_actions)
        self.buttons.append(back_btn)

        # Refresh the screen to show the move buttons
        self.update_display()

    def opponent_turn(self):
        """Let the AI opponent take a turn."""
        moves = self.trainer2.current_pokemon.moves
        chosen_move = random.choice(moves)
        
        # Execute the chosen move
        self.execute_move(chosen_move)
        
        # Check if player's Pokémon is defeated
        if self.trainer1.current_pokemon.current_health <= 0:
            # Handle player Pokémon defeat here
            self.handle_fainted_pokemon_pygame(self.trainer2.current_pokemon, self.trainer1.current_pokemon)
            if all(pokemon.current_health <= 0 for pokemon in self.trainer1.pokemon_list):
                print(f"{self.trainer2.name} won the battle!")
                self.exit_battle()

    def execute_move(self, move):
        # Existing code to execute the move
        move.use(self.current_trainer.current_pokemon, self.current_trainer.opponent.current_pokemon)

        # Update display
        self.display_pokemon(self.current_trainer.opponent, 500, 50)

        # Check if either Pokémon has fainted
        if self.current_trainer.current_pokemon.current_health <= 0:
            self.handle_fainted_pokemon_pygame(self.current_trainer.opponent.current_pokemon, self.current_trainer.current_pokemon)
        elif self.current_trainer.opponent.current_pokemon.current_health <= 0:
            self.handle_fainted_pokemon_pygame(self.current_trainer.current_pokemon, self.current_trainer.opponent.current_pokemon)
        else:
            # Switch turns only if no Pokémon has fainted
            self.current_trainer = self.trainer2 if self.current_trainer == self.trainer1 else self.trainer1
            if self.current_trainer == self.trainer2:
                self.opponent_turn()
            else:
                # Return to main action buttons after player's move is executed
                self.back_to_main_actions()

    


    def back_to_main_actions(self):
        # Reset the flag and offset
        self.show_scrollbar = False
        self.scroll_offset = 0
        # Reset the main action buttons
        self.buttons = [
            Button(self.button_a_xpos, self.button_a_ypos, self.button_width, self.button_height, "MOVE", function=self.choose_move_pygame),
            Button(self.button_b_xpos, self.button_b_ypos, self.button_width, self.button_height, "SWITCH", function=self.choose_switch_pygame),
            Button(self.button_c_xpos, self.button_c_ypos, self.button_width, self.button_height, "ITEM", function=self.choose_item_pygame),
            Button(self.button_d_xpos, self.button_d_ypos, self.button_width, self.button_height, "ATTACK", function=self.choose_attack_pygame),
            Button(self.button_e_xpos, self.button_e_ypos, self.button_width, self.button_height, "EXIT", function=self.exit_battle)  # New exit button
        ]
        self.update_display()

    def choose_switch_pygame(self):
        # Clear current buttons
        self.buttons.clear()

        # Define fonts
        font = pygame.font.Font(font_path, 32)  # For Pokémon name
        small_font = pygame.font.Font(font_path, 16)  # For HP

        btn_width, btn_height = self.button_width, self.button_height
        spacing = 25
        initial_x, initial_y = 20, 660

        # Determine x and y for the buttons
        valid_pokemon = [pokemon for pokemon in self.trainer1.pokemon_list if pokemon != self.trainer1.current_pokemon and pokemon.current_health > 0]
        for i, pokemon in enumerate(valid_pokemon):
            row = i // 3
            col = i % 3
            x = initial_x + (btn_width + spacing) * col
            y = initial_y + (btn_height + spacing) * row

            pokemon_name_surface = font.render(pokemon.name.upper(), True, (255, 255, 255))
            hp_surface = small_font.render(f"(HP: {pokemon.current_health}/{pokemon.max_health})", True, (255, 255, 255))
            
            combined_height = pokemon_name_surface.get_height() + hp_surface.get_height()
            combined_text = pygame.Surface((btn_width, combined_height), pygame.SRCALPHA, 32)
            combined_text.blit(pokemon_name_surface, (0, 0))
            combined_text.blit(hp_surface, (0, pokemon_name_surface.get_height()))

            btn = Button(x, y, btn_width, btn_height + combined_height - font.get_height(), combined_text, function=self.execute_switch, params=[pokemon])
            self.buttons.append(btn)

        # Add a 'Go Back' button
        x_back = initial_x + (btn_width + spacing) * 2  # Adjust if needed
        y_back = initial_y + (btn_height + spacing) * -1  # Adjust if needed
        back_btn = Button(x_back, y_back, btn_width, btn_height, "BACK", function=self.back_to_main_actions)
        self.buttons.append(back_btn)

        # Refresh the screen to show the Pokémon switch buttons
        self.update_display()

    def force_switch_menu(self):
        # Bring up the switch menu
        self.choose_switch_pygame()

        # Wait for the player to make a choice
        switching = True
        while switching:
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    pygame.quit()
                    return
                elif event.type == pygame.MOUSEBUTTONUP:
                    for btn in self.buttons:
                        if btn.is_over(pygame.mouse.get_pos()):
                            btn.function(*btn.params)
                            switching = False
                            break

            # Update display here if necessary
            self.update_display()
            self.clock.tick(30)


    def handle_fainted_pokemon_pygame(self, attacker, defender):
        """Handle the scenario when a Pokémon is defeated."""
        # Defender Pokémon fainted
        print(f"{defender.name} has fainted!")
        print(f"attacker experince: {attacker.experience}")
        
        # Check if it's the player's Pokémon that fainted
        if defender == self.trainer1.current_pokemon:
            # Check if the player has other Pokémon that aren't fainted
            experience_gain = defender.level * 10  # Example calculation
            attacker.gain_experience(experience_gain, self.trainer2.moves_dict)
            alive_pokemon = [pokemon for pokemon in self.trainer1.pokemon_list if pokemon.current_health > 0]
            if not alive_pokemon:
                # All player Pokémon are fainted
                print(f"{self.trainer2.name} won the battle!")
                self.exit_battle()
                return
            else:
                # Let the player choose another Pokémon
                self.force_switch_menu()

        # Check if it's the opponent's Pokémon that fainted
        # Handle if defender is the opponent's Pokémon
        elif defender == self.trainer2.current_pokemon:
            experience_gain = defender.level * 1000  # Example calculation
            attacker.gain_experience(experience_gain, self.trainer1.moves_dict)

            alive_pokemon = [pokemon for pokemon in self.trainer2.pokemon_list if pokemon.current_health > 0]
            if not alive_pokemon:
                # All opponent Pokémon are fainted
                print(f"{self.trainer1.name} won the battle!")
                # Here, we call the post_battle_summary function
                self.post_battle_summary(self.screen, self.human_trainer, self.game_state)
            else:
                # The AI chooses another Pokémon
                new_pokemon = random.choice(alive_pokemon)
                self.trainer2.current_pokemon = new_pokemon
                print(f"{self.trainer2.name} switched to {new_pokemon.name}!")
                # Update the opponent's Pokémon image
                self.update_pokemon_image(self.trainer2)
                # Update the display
                self.update_display()
                # Switch back to player's turn
                self.current_trainer = self.trainer1

    def update_pokemon_image(self, trainer):
        """Update the Pokémon image based on the trainer's current Pokémon."""
        if trainer == self.trainer1:
            self.trainer1_pokemon_image = pygame.image.load(self.get_pokemon_image_path(trainer.current_pokemon.name))
            self.screen.blit(self.trainer1_pokemon_image, (50, 150))
        else:
            print(f"update pokemon image:  {trainer.current_pokemon.name}")
            self.trainer2_pokemon_image = pygame.image.load(self.get_pokemon_image_path(trainer.current_pokemon.name))
            self.screen.blit(self.trainer2_pokemon_image, (500, 150))
        
        # Update the display
        pygame.display.flip()

    def execute_switch(self, chosen_pokemon):
        # Switch the current Pokémon
        self.trainer1.current_pokemon = chosen_pokemon

        # Update the Pokémon image for the player
        self.update_pokemon_image(self.trainer1)

        # If it's the opponent's turn, also update the opponent's Pokémon image
        if self.current_trainer == self.trainer2:
            self.update_pokemon_image(self.trainer2)
            
        # Possibly add any other logic you want when the switch happens, like printing a message.
        if self.current_trainer == self.trainer1:
            self.current_trainer = self.trainer2
        else:
            self.current_trainer = self.trainer1

        self.back_to_main_actions()
    
    def choose_item_pygame(self):
        # Clear current buttons
        self.buttons.clear()

        # Define fonts
        font = pygame.font.Font(font_path, 24)  # For item name
        small_font = pygame.font.Font(font_path, 12)  # For quantity

        btn_width, btn_height = self.button_width, self.button_height
        spacing = 25
        initial_x, initial_y = 20, 660

        # Determine x and y for the buttons
        for i, item_info in enumerate(self.trainer1.items):
            item = item_info[0]  # The Item object is at index 0
            quantity = item_info[1]  # The quantity is at index 1
            if quantity > 0:
                row = i // 3
                col = i % 3
                x = initial_x + (btn_width + spacing) * col
                y = initial_y + (btn_height + spacing) * row

                item_name_surface = font.render(item.name.upper(), True, (255, 255, 255))
                quantity_surface = small_font.render(f"(x{quantity})", True, (255, 255, 255))
                
                combined_height = item_name_surface.get_height() + quantity_surface.get_height()
                combined_text = pygame.Surface((btn_width, combined_height), pygame.SRCALPHA, 32)
                combined_text.blit(item_name_surface, (0, 0))
                combined_text.blit(quantity_surface, (0, item_name_surface.get_height()))

                btn = Button(x, y, btn_width, btn_height + combined_height - font.get_height(), combined_text, function=self.select_item, params=[item])
                self.buttons.append(btn)

        # Add a 'Go Back' button
        x_back = initial_x + (btn_width + spacing) * 2  # Adjust if needed
        y_back = initial_y + (btn_height + spacing) *- 1 # Adjust based on the number of items
        back_btn = Button(x_back, y_back, btn_width, btn_height, "BACK", function=self.back_to_main_actions)
        self.buttons.append(back_btn)

        # Refresh the screen to show the item buttons
        self.update_display()

    # Callback function to select an item
    def select_item(self, item):
        self.selected_item = item
        print(f"select_item selected item: {self.selected_item.name}")
        self.item_selected = True  # Set the flag to True when an item is selected
        print("select_item method")
        print(f"select_item item target: {item.target}")
        
        # Modified check for the item.target
        if isinstance(item.target, str):
            target_value = item.target
        elif isinstance(item.target, dict):
            target_value = list(item.target.keys())[0]
        elif isinstance(item.target, set):
            target_value = next(iter(item.target))
        else:
            print("Unknown item target type!")
            return

        # Now use target_value in the checks:
        if target_value == 'choose_own_pokemon':
            print("!!!!!select_item method choose_own_pokemon")
            self.choose_pokemon_pygame()

        elif item.target == 'choose_opp_pokemon':
            print("select_item method choose_opp_pokemon")
            self.choose_opponent_pokemon_pygame()
        elif item.target == 'current_opp_pokemon':
            print("select_item method current_opp_pokemon")
            if any(effect_type in item.effect for effect_type in ["capture"]):  # Check if the item effect is capture
                print("select_item capture")
                print(f"item effect: {item.effect}")
                current_wild_pokemon = self.get_wild_pokemon_target()
                print(f"current wild pokemon: {current_wild_pokemon}")
                self.execute_item(item=self.selected_item, wild_pokemon=current_wild_pokemon)

        elif item.target == 'opp_trainer':
            print("select_item method opp_trainer")
            trainer = self.get_opponent_trainer_target()
            self.execute_item(item=self.selected_item, trainer=trainer)
            self.decrement_item_quantity(self.selected_item)
        elif item.target == 'human_trainer':
            print("select_item method human_trainer")
            trainer = self.get_human_trainer_target()
            self.execute_item(item=self.selected_item, trainer=trainer)
            self.decrement_item_quantity(self.selected_item)
        elif item.target == 'all_opp_pokemon':
            print("select_item method all_opp_pokemon")
            selected_pokemon_list = self.get_all_opponent_pokemon_target()
            print(item.item_type)
            if item.item_type == "Spell":
                print("INSIDE SPELL")
                for pokemon in selected_pokemon_list:
                    print(pokemon.name)
                    print(item.name)
                    self.set_selected_pokemon_and_execute_item(pokemon=pokemon, item=self.selected_item)
                self.trainer1.mana_spent = False
            else:
                print("INSIDE ELSE")
                for pokemon in selected_pokemon_list:
                    print(pokemon.name)
                    print(item.name)
                    self.set_selected_pokemon_and_execute_item(pokemon=pokemon, item=self.selected_item)
            self.item_selected = False
            self.selected_item = None  # Clear the selected item here.

        elif item.target == 'all_own_pokemon':
            print("select_item method all_own_pokemon")
            selected_pokemon_list = self.get_all_own_pokemon_target()
            for pokemon in selected_pokemon_list:
                print(pokemon.name)
                print(item.name)
                self.set_selected_pokemon_and_execute_item(pokemon=pokemon, item=self.selected_item)
            self.item_selected = False
            self.selected_item = None  # Clear the selected item here.
        else:
            # If the item's target is not recognized, return to the main actions menu
            self.back_to_main_actions()

    def get_selected_pokemon_target(self):
        return self.selected_pokemon
    
    def get_wild_pokemon_target(self):
        return self.wild_pokemon_target

    def get_selected_trainer_target(self):
        return self.selected_trainer

    def set_selected_pokemon_and_execute_item(self, pokemon, item):
        self.selected_pokemon = pokemon
        self.selected_item = item
        print(f"selected pokemon: {self.selected_pokemon.name}")
        print(f"selected pokemon: {self.selected_pokemon.name} and selected item: {self.selected_item.name}")
        self.execute_item(item=self.selected_item, pokemon=pokemon)
        self.decrement_item_quantity(self.selected_item)

    def set_selected_trainer_and_execute_item(self, trainer, item):
        self.selected_trainer = trainer
        self.selected_item = item
        print(f"selected trainer: {self.selected_trainer.name}")
        print(f"selected trainer: {self.selected_trainer.name} and selected item: {self.selected_item.name}")
        self.execute_item(item=self.selected_item, trainer=trainer)
        self.decrement_item_quantity(self.selected_item)

    def set_selected_move_and_execute_item(self, move):
        self.selected_move = move
        print(f"Selected move: {self.selected_move.name} for Pokemon: {self.selected_pokemon.name}")
        # Use the selected item on the selected move of the selected Pokémon
        self.execute_item(item=self.selected_item, pokemon=self.selected_pokemon, move=self.selected_move)
        self.decrement_item_quantity(self.selected_item)

    # In the PygameBattle class, pass the callable function as the target
    def execute_item(self, item, pokemon=None, trainer=None, move=None, wild_pokemon=None):
        spells_chart = self.spells_chart
        quantity=1
        print(f"execute_item wild pokemon: {wild_pokemon}")
        # Determine the target for the item based on the available information
        if pokemon:
            print(f"NEW execute_item selected pokemon: {pokemon.name} and selected item: {item.name}")
            target = self.get_selected_pokemon_target
        elif wild_pokemon:
            print(f"NEW execute_item selected pokemon: {wild_pokemon.name} and selected item: {item.name}")
            target = self.get_wild_pokemon_target
        elif trainer:
            print(f"NEW execute_item selected trainer: {trainer.name} and selected item: {item.name}")
            target = self.get_selected_trainer_target
        else:
            print("execute_item: No valid target selected for execution.")
            return

        if not self.item_selected or not self.selected_item:
            print("execute_item: No item selected for execution.")
            return

        if self.item_selected:
            # Check if an item is selected
            print(f"execute_item: Item Target: {item.target}")
            print(f"execute_item: Item Name: {item.name}")
            # Call the use_item method based on the determined target
            # Determine the target for the item based on the available information
            if pokemon and move:
                self.trainer1.use_item(lambda: move, pokemon, item, quantity, spells_chart)
            elif pokemon:
                self.trainer1.use_item(target, pokemon, item, quantity, spells_chart)
            elif wild_pokemon:
                self.trainer1.use_item(self.get_wild_pokemon_target, wild_pokemon, item, quantity, spells_chart)
            elif trainer:
                self.trainer1.use_item(lambda: trainer, trainer, item, quantity, spells_chart)

            # Decrement the item quantity after it's been used
            #self.trainer1.update_item_quantity(item)

        # Clear the item selection flag and item AFTER executing the item's effect
        #self.item_selected = False
        #self.selected_item = None
        self.selected_pokemon = None

        # Return to the main actions menu
        self.back_to_main_actions()

    def choose_pokemon_pygame(self):
        # Clear the screen, buttons, and set the flag
        self.screen.fill((255, 255, 255))
        self.buttons.clear()  # Clear any existing buttons
        self.show_scrollbar = True
        print(f"choose_pokemon_pygame selected item name: {self.selected_item.name}")
        item = self.selected_item
        print(f"item : {item.name}")

        btn_width, btn_height = 225, 50
        spacing = 20
        initial_x, initial_y = 50, 580

        # Add a 'Go Back' button regardless of whether an item is selected or not
        back_btn = Button(initial_x + btn_width + spacing, 20, btn_width, btn_height, "Go Back", function=self.back_to_main_actions)
        self.buttons.append(back_btn)

        # Determine x and y for the buttons
        for i, pokemon in enumerate(self.trainer1.pokemon_list):
            row = i // 3
            col = i % 3
            x = initial_x + (btn_width + spacing) * col
            y = initial_y + (btn_height + spacing) * row

            if pokemon.current_health > 0:
                btn_text = f"{pokemon.name} (HP: {pokemon.current_health}/{pokemon.max_health})"
                if self.selected_item:
                    # Check the item type and adjust the function accordingly
                    if any(effect_type in item.effect for effect_type in ["increase_pp", "increase_accuracy"]):
                        btn = Button(x, y, btn_width, btn_height, btn_text, function=self.choose_move_for_ppup_pygame, params=[pokemon])
                    elif "teach_move" in item.effect:
                        tm_move = item.move
                        btn = Button(x, y, btn_width, btn_height, btn_text, function=self.choose_move_to_replace_pygame, params=[pokemon, tm_move])
                    else:
                        btn = Button(x, y, btn_width, btn_height, btn_text, function=self.set_selected_pokemon_and_execute_item, params=[pokemon, item])
                else:
                    # Display the "choose_own_pokemon" menu without item use
                    btn = Button(x, y, btn_width, btn_height, btn_text, function=self.set_selected_pokemon_and_execute_item, params=[pokemon, item])
                self.buttons.append(btn)

        # Refresh the screen to show the Pokémon buttons
        self.update_display()

    def choose_opponent_pokemon_pygame(self):
        # Clear the screen and set the flag
        self.screen.fill((255, 255, 255))
        self.show_scrollbar = True
        print(f"choose_pokemon_pygame selected item name: {self.selected_item.name}")
        item = self.selected_item
        print(f"item : {item.name}")
        # Check if an item is selected
        if self.selected_item:
            # Display the "choose_own_pokemon" menu for item use
            y_pos = 100  # Adjust the initial y position as needed
            for i, pokemon in enumerate(self.trainer2.pokemon_list):
                if pokemon.current_health > 0:
                    btn_text = f"{pokemon.name} (HP: {pokemon.current_health}/{pokemon.max_health})"
                    btn = Button(100, y_pos, 250, 50, btn_text, function=self.set_selected_pokemon_and_execute_item, params=[pokemon, item])
                    self.buttons.append(btn)
                    y_pos += 60  # Adjust for the next button's position

            # Add a 'Go Back' button
            back_btn = Button(300, y_pos, 250, 50, "Go Back", function=self.back_to_main_actions)
            self.buttons.append(back_btn)
        else:
            # Display the "choose_own_pokemon" menu without item use
            y_pos = 100  # Adjust the initial y position as needed
            for i, pokemon in enumerate(self.trainer2.pokemon_list):
                if pokemon.current_health > 0:
                    btn_text = f"{pokemon.name} (HP: {pokemon.current_health}/{pokemon.max_health})"
                    btn = Button(100, y_pos, 250, 50, btn_text, function=self.set_selected_pokemon_and_execute_item, params=[pokemon, item])
                    self.buttons.append(btn)
                    y_pos += 60  # Adjust for the next button's position

            # Add a 'Go Back' button
            back_btn = Button(300, y_pos, 250, 50, "Go Back", function=self.back_to_main_actions)
            self.buttons.append(back_btn)

        # Refresh the screen to show the Pokémon buttons
        self.update_display()
    
    def choose_pokemon_for_ppup_pygame(self):
        # Clear the screen and set the flag
        self.screen.fill((255, 255, 255))
        self.show_scrollbar = True

        y_pos = 100  # Adjust the initial y position as needed
        for i, pokemon in enumerate(self.trainer1.pokemon_list):
            if pokemon.current_health > 0:
                btn_text = f"{pokemon.name} (HP: {pokemon.current_health}/{pokemon.max_health})"
                btn = Button(100, y_pos, 250, 50, btn_text, function=self.choose_move_for_ppup_pygame, params=[pokemon])
                self.buttons.append(btn)
                y_pos += 60  # Adjust for the next button's position

        # Add a 'Go Back' button
        back_btn = Button(300, y_pos, 250, 50, "Go Back", function=self.back_to_main_actions)
        self.buttons.append(back_btn)

        # Refresh the screen to show the Pokémon buttons
        self.update_display()
    
    def choose_move_for_ppup_pygame(self, pokemon):
        # Clear current buttons
        self.buttons.clear()
        self.selected_pokemon = pokemon  # Store the selected Pokémon

        # Add a button for each move the selected Pokémon knows
        y_pos = 450
        for index, move in enumerate(pokemon.moves, start=1):
            btn = Button(100, y_pos, 250, 50, f"{move.name} (PP: {move.pp}/{move.max_pp})", function=self.set_selected_move_and_execute_item, params=[move])
            self.buttons.append(btn)
            y_pos += 60  # Adjust for next button's position

        # Add a 'Go Back' button
        back_btn = Button(300, y_pos, 250, 50, "Go Back", function=self.back_to_main_actions)
        self.buttons.append(back_btn)

        # Refresh the screen to show the move buttons
        self.update_display()

    def choose_move_to_replace_pygame(self, pokemon, tm_move):
        """Display the moves of the selected Pokémon and prompt the player to replace a move."""
        self.screen.fill((255, 255, 255))
        self.buttons.clear()  # Clear any existing buttons
        y_pos = 100

        # List the Pokémon's current moves
        for i, move in enumerate(pokemon.moves):
            btn_text = f"{move.name}"
            btn = Button(300, y_pos, 250, 50, btn_text, function=self.replace_move, params=[pokemon, move, tm_move])
            self.buttons.append(btn)
            y_pos += 60

        # If the Pokémon knows fewer than four moves, offer an option to simply learn the new move
        if len(pokemon.moves) < 4:
            btn_text = "Learn new move without replacing"
            btn = Button(100, y_pos, 350, 50, btn_text, function=self.add_new_move, params=[pokemon, tm_move])
            self.buttons.append(btn)
            y_pos += 60

        # Add a 'Go Back' button
        back_btn = Button(300, y_pos, 250, 50, "Go Back", function=self.back_to_main_actions)
        self.buttons.append(back_btn)

        # Refresh the screen
        self.update_display()

    def replace_move(self, pokemon, old_move, new_move):
        """Replace an old move with a new move for the selected Pokémon."""
        index = pokemon.moves.index(old_move)
        pokemon.moves[index] = new_move
        print(f"{pokemon.name} forgot {old_move.name} and learned {new_move.name}!")
        self.back_to_main_actions()
        
    def add_new_move(self, pokemon, new_move):
        """Add a new move to the Pokémon's moveset."""
        pokemon.moves.append(new_move)
        print(f"{pokemon.name} learned {new_move.name}!")

    def get_opponent_trainer_target(self):
        return self.trainer2

    def get_human_trainer_target(self):
        return self.trainer1

    def get_all_opponent_pokemon_target(self):
        return self.trainer2.pokemon_list

    def get_all_own_pokemon_target(self):
        return self.trainer1.pokemon_list

    def decrement_item_quantity(self, item):
        for i, (itm, qty) in enumerate(self.trainer1.items):
            if itm == item:
                # Decrement the quantity
                self.trainer1.items[i] = (itm, qty - 1)

                # Remove the item if its quantity becomes zero
                if self.trainer1.items[i][1] <= 0:
                    self.trainer1.items.pop(i)
                break






    def choose_attack_pygame(self):
        opponent_pokemon = self.trainer2.current_pokemon  # Assuming trainer2 is always the opponent
        if opponent_pokemon is not None:
            # Calculate the damage
            damage = (self.trainer1.current_pokemon.attack / opponent_pokemon.defense) * 10
            damage = round(damage)  # Round the damage to a whole number
            opponent_pokemon.current_health = max(0, opponent_pokemon.current_health - damage)

            # Display the result on the screen (you might want to implement a more sophisticated display method)
            print(f"{self.trainer1.current_pokemon.name} attacked {opponent_pokemon.name} for {damage} damage!")
            print(f"{opponent_pokemon.name} now has {opponent_pokemon.current_health} health remaining.")

            # Check if opponent's Pokémon is defeated
            if opponent_pokemon.current_health <= 0:
                print(f"{opponent_pokemon.name} has been defeated!")
                experience_gain = opponent_pokemon.level * 100  # Example calculation
                self.trainer1.current_pokemon.gain_experience(experience_gain, self.moves_dict)
                alive_pokemon = [pokemon for pokemon in self.trainer2.pokemon_list if pokemon.current_health > 0]
                if not alive_pokemon:
                    # All opponent Pokémon are fainted
                    print(f"{self.trainer1.name} won the battle!")
                    self.post_battle_summary(self.screen, self.human_trainer, self.game_state)
                else:
                    # The AI chooses another Pokémon randomly
                    new_pokemon = random.choice(alive_pokemon)
                    self.trainer2.current_pokemon = new_pokemon
                    print(f"{self.trainer2.name} switched to {new_pokemon.name}!")
                    # Update the opponent's Pokémon image
                    self.update_pokemon_image(self.trainer2)

            else:
                # Switch to the opponent's turn after executing an attack
                self.current_trainer = self.trainer2
                self.opponent_turn()

        else:
            print("There is no opponent Pokemon to attack.")

        # Switch back to player's turn after opponent's turn is complete
        self.current_trainer = self.trainer1

        # Return to main actions after the attack
        self.back_to_main_actions()

    def exit_battle(self):
        self.post_battle_summary(self.screen, self.human_trainer, self.game_state)



    def post_battle_summary(self, screen, human_trainer, game_state):
        # Load background and GIFs
        bg_image, gif_images, gif_images_middle, gif_images_top = self.load_resources()

        # Initialize frame counters for GIF animations
        current_frame_original = 0
        current_frame_middle = 5
        current_frame_top = 10
        frame_counter = 0
        frame_update_rate = 2  # Adjust this as needed for the GIF frame update rate
        # Display coins earned, experience gained, and current health of Pokemon
        #font_path = "pixeled.ttf"

        font = pygame.font.Font(self.font_path, 24)
        y_pos = 50
        y_increment = 60

        # Get the screen dimensions for centering
        screen_width, screen_height = screen.get_size()

        
        def get_pokemon_image_path(pokemon_name):
            """Return the path to the image for the given Pokémon."""
            pokemon_details = game_state['pokemons'].get(pokemon_name)  # Use game_state to access pokemons
            if not pokemon_details:
                raise ValueError(f"No Pokemon found with the name {pokemon_name}")

            try:
                pokemon_index = pokemon_details.index
                formatted_index = f"{pokemon_index:04}"  # Zero-pad the index to ensure it's 4 digits
            except ValueError:
                raise ValueError(f"No Pokemon found with the name {pokemon_name}")
                    
            #return os.path.join("F:\\Scripts\\PokePyMain-main\\pokemon_pics", f"{formatted_index}{pokemon_name}.png")
            #return os.path.join("C:\\Users\matth\\OneDrive\\PokePy\\PokePyMain-main\\pokemon_pics", f"{formatted_index}{pokemon_name}.png")
            #return os.path.join("C:\\Users\Tusa\\OneDrive\\PokePy\\PokePyMain-main\\pokemon_pics", f"{formatted_index}{pokemon_name}.png")
    
            return os.path.join("pokemon_pics", f"{formatted_index}{pokemon_name}.png")


        max_total_human_trainer_pokemon_list_health = 0
        current_total_human_trainer_pokemon_list_health = 0

        for pokemon in human_trainer.pokemon_list:
            max_total_human_trainer_pokemon_list_health += pokemon.max_health
            print(f"max_total_human_trainer_pokemon_list_health: {max_total_human_trainer_pokemon_list_health}")

        for pokemon in human_trainer.pokemon_list:
            current_total_human_trainer_pokemon_list_health += pokemon.current_health
            print(f"current_total_human_trainer_pokemon_list_health: {current_total_human_trainer_pokemon_list_health}")

        current_human_trainer_pokemon_list_health_percent = current_total_human_trainer_pokemon_list_health/max_total_human_trainer_pokemon_list_health
        coin_win_amount = int((self.trainer2.coins*current_human_trainer_pokemon_list_health_percent)/2)

        print(f"{self.trainer2.name}'s coin amount: {self.trainer2.coins}")

        self.trainer1.coins=self.trainer1.coins+coin_win_amount
        print(f"Trainer 1 Coins: {self.trainer1.coins}")

      # Create messages to display
        coins_earned_msg = f"COINS EARNED: {coin_win_amount}"  # Assuming you keep track of coins earned in the trainer object
        total_coins_msg = f"TOTAL COINS: {self.trainer1.coins}" 
        messages = [coins_earned_msg, total_coins_msg]

        # Create Pokémon health messages outside the main loop
        pokemon_health_messages = [f"{pokemon.name.upper()}: {pokemon.current_health}/{pokemon.max_health}" for pokemon in human_trainer.pokemon_list]

        # Initialize button navigation variables
        selected_button_index = 0
        using_keyboard = False

        # Create buttons
        battle_again_btn = Button(440, y_pos + len(messages) * y_increment + 420, 400, 100, "BATTLE", function=choose_battle_menu_pygame, params=[screen, game_state, human_trainer, game_state['trainers'], game_state['moves'], game_state['pokemons']])
        back_to_menu_btn = Button(440, y_pos + len(messages) * y_increment + 540, 400, 100, "MENU", function=pre_battle_menu_pygame, params=[screen, game_state, human_trainer])
        # Create "Explore Mode" button
        # In the post_battle_summary function
        # Corrected button initialization for 'Explore Mode'
        explore_mode_btn = Button(
            440, y_pos + len(messages) * y_increment + 660, 400, 100, "EXPLORE",
            function=explore, 
            params=[screen, human_trainer, game_state['items'], game_state['trainers'], game_state['pokemons'], game_state, game_state['moves']]
        )
        buttons = [battle_again_btn, back_to_menu_btn, explore_mode_btn]

        # Post-battle summary loop

        # Post-battle summary loop
        running = True
        while running:
            mouse_up = False
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    running = False
                elif event.type == pygame.MOUSEBUTTONUP:
                    mouse_up = True
                elif event.type == pygame.KEYDOWN:
                    if event.key == pygame.K_UP:
                        selected_button_index = (selected_button_index - 1) % len(buttons)
                        using_keyboard = True
                    elif event.key == pygame.K_DOWN:
                        selected_button_index = (selected_button_index + 1) % len(buttons)
                        using_keyboard = True
                    elif event.key == pygame.K_RETURN:
                        buttons[selected_button_index].clicked = True
                        if buttons[selected_button_index].function:
                            buttons[selected_button_index].function(*buttons[selected_button_index].params if buttons[selected_button_index].params else [])

            # Clear the screen
            screen.fill((255, 255, 255))

            # Get screen size for centering
            screen_width, screen_height = screen.get_size()

            # Get the size of the scaled background image and calculate offsets
            bg_width, bg_height = bg_image.get_size()
            bg_x_offset = (bg_width - screen_width) // 2
            bg_y_offset = (bg_height - screen_height) // 2

            # Blit the centered background
            screen.blit(bg_image, (-bg_x_offset, -bg_y_offset))

            # Update and display GIF frames at a slower rate
            frame_counter = (frame_counter + 1) % frame_update_rate
            if frame_counter == 0:
                # Increment and get current GIF frames
                current_frame_original = (current_frame_original + 1) % len(gif_images)
                current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
                current_frame_top = (current_frame_top + 1) % len(gif_images_top)

            # Blit the GIF frames
            screen.blit(gif_images[current_frame_original], (800, 600))
            screen.blit(gif_images_middle[current_frame_middle], (0, 0))
            screen.blit(gif_images_top[current_frame_top], (0, 0))

            

            # Create a semi-transparent surface for the Pokemon list background
            pokemon_list_background_width = 500  # Adjust the width as needed
            pokemon_list_background_height = len(pokemon_health_messages) * y_increment + 40  # Calculate the height dynamically
            pokemon_list_background = pygame.Surface((pokemon_list_background_width, pokemon_list_background_height), pygame.SRCALPHA)
            teal_color = (0, 128, 128, 191)  # Teal color with 75% opacity
            white_color = (255, 255, 255)
            border_radius = 15  # Radius of the rounded corners

            # Draw a rounded rectangle with the teal color
            pygame.draw.rect(pokemon_list_background, teal_color, pokemon_list_background.get_rect(), border_radius=border_radius)
            
            # Optionally draw a white border with rounded corners on top
            pygame.draw.rect(pokemon_list_background, white_color, pokemon_list_background.get_rect(), 12, border_radius=border_radius)

            # Calculate the position to center the background on the screen
            background_x_position = (screen_width - pokemon_list_background_width) // 2
            background_y_position = y_pos + len(messages) * y_increment - 10  # Adjust as needed

            # Blit the semi-transparent background onto the screen
            screen.blit(pokemon_list_background, (background_x_position, background_y_position))



            # Render and display coin messages at the top centered
            for i, msg in enumerate(messages):
                text = font.render(msg, True, (255, 255, 255))
                text_rect = text.get_rect(center=(screen_width // 2, y_pos + i * y_increment))
                screen.blit(text, text_rect)

            # Adjust y_pos for Pokémon messages
            adjusted_y_pos = y_pos + len(messages) * y_increment

            # Blit Pokémon images and their health stats centered
            for i, health_msg in enumerate(pokemon_health_messages):
                pokemon = human_trainer.pokemon_list[i]

                # Load and display the image of the Pokémon
                pokemon_image = pygame.image.load(get_pokemon_image_path(pokemon.name))
                scaled_pokemon_image = pygame.transform.scale(pokemon_image, (80, 80))
                
                # Center the image and text horizontally
                image_x_position = (screen_width - (scaled_pokemon_image.get_width() + 400)) // 2
                text_x_position = image_x_position + scaled_pokemon_image.get_width() + 10
                
                # Position the image and text vertically
                image_y_position = adjusted_y_pos + i * y_increment
                text_y_position = image_y_position
                
                screen.blit(scaled_pokemon_image, (image_x_position, image_y_position))
                health_text = font.render(health_msg, True, (255, 255, 255))
                screen.blit(health_text, (text_x_position, text_y_position))

            # Update and draw buttons
            for i, button in enumerate(buttons):
                button.highlighted = (i == selected_button_index)
                button.update(pygame.mouse.get_pos(), mouse_up, keyboard_navigation=using_keyboard)
                button.draw(screen)

            pygame.display.flip()
            pygame.time.Clock().tick(60)



    def display_pokemon(self, trainer, x, y):
        # Scale the Pokémon image to 300x300 pixels
        if trainer == self.trainer1:
            scaled_pokemon_image = pygame.transform.scale(self.trainer1_pokemon_image, (200, 200))
            self.screen.blit(scaled_pokemon_image, (x + 100, y + 225))  # Adjust y-position as needed
        else:
            scaled_pokemon_image = pygame.transform.scale(self.trainer2_pokemon_image, (200, 200))
            self.screen.blit(scaled_pokemon_image, (x - 50, y + 225))  # Adjust y-position as needed

        # Create a smaller font instance for HP and EXP texts
        small_font = pygame.font.Font(font_path, 10)

        # Health bar settings
        bar_width = 250
        bar_height = 5
        
        pokemon_healthbar_height = 8
        # Pokémon's Health Percentage
        current_health_percentage = 0 if trainer.current_pokemon.max_health == 0 else trainer.current_pokemon.current_health / trainer.current_pokemon.max_health
        health_bar_width = int(current_health_percentage * bar_width)
        trainer_bar_max_width = 75
        pokemon_exp_bar_max_width = 125

        # Determine the color of the health bar
        if current_health_percentage < 0.1:
            health_color = (255, 0, 0)  # Red
        elif current_health_percentage < 0.25:
            health_color = (255, 165, 0)  # Orange
        else:
            health_color = (0, 255, 0)  # Green

        # Draw the background of the health bar (grayed out)
        pygame.draw.rect(self.screen, (170, 170, 170), (x, y + 65, bar_width, pokemon_healthbar_height))
        # Draw the current health
        pygame.draw.rect(self.screen, health_color, (x, y + 65, health_bar_width, pokemon_healthbar_height))

        # Trainer's Health Bar
        trainer_health_percentage = 0 if trainer.max_health == 0 else trainer.current_health / trainer.max_health
        trainer_health_bar_width = int(trainer_health_percentage * trainer_bar_max_width)
        trainer_health_color = (0, 255, 0) if trainer_health_percentage > 0.25 else (255, 165, 0) if trainer_health_percentage > 0.1 else (255, 0, 0)
        pygame.draw.rect(self.screen, (170, 170, 170), (x, y, trainer_bar_max_width, bar_height))
        pygame.draw.rect(self.screen, trainer_health_color, (x, y, trainer_health_bar_width, bar_height))

        # Trainer's Mana Bar
        #print(f"trainer.mana = {trainer.mana}")
        #print(f"trainer.max_mana = {trainer.max_mana}")
        trainer_mana_percentage = 0 if trainer.max_mana == 0 else trainer.mana / trainer.max_mana
        trainer_mana_bar_width = int(trainer_mana_percentage * trainer_bar_max_width)
        trainer_mana_color = (0, 0, 255)
        pygame.draw.rect(self.screen, (170, 170, 170), (x, y + 10, trainer_bar_max_width, bar_height))
        pygame.draw.rect(self.screen, trainer_mana_color, (x, y + 10, trainer_mana_bar_width, bar_height))

        # Pokémon's Experience Bar
        pokemon_exp_percentage = 0 if trainer.current_pokemon.level_up_experience == 0 else trainer.current_pokemon.experience / trainer.current_pokemon.level_up_experience
        pokemon_exp_bar_width = int(pokemon_exp_percentage * pokemon_exp_bar_max_width)
        pokemon_exp_color = (255, 223, 0)
        pygame.draw.rect(self.screen, (170, 170, 170), (x, y + 95, pokemon_exp_bar_max_width, bar_height))
        pygame.draw.rect(self.screen, pokemon_exp_color, (x, y + 95, pokemon_exp_bar_width, bar_height))

        # Display Pokémon name and health
        trainer_text = small_font.render(f"{trainer.name.upper()} : {trainer.current_health} / {trainer.max_health}", True, (0, 0, 0))
        pokemon_text = self.font.render(f"{trainer.current_pokemon.name.upper()} : {trainer.current_pokemon.level}", True, (0, 0, 0))

        hp_text = small_font.render(f"HP: {int(trainer.current_pokemon.current_health)}/{int(trainer.current_pokemon.max_health)}", True, (0, 0, 0))
        exp_text = small_font.render(f"EXP: {int(trainer.current_pokemon.experience)}/{int(trainer.current_pokemon.level_up_experience)}", True, (0, 0, 0))


        # Assuming the status is a string like "Healthy", "Poisoned", etc.
        pokemon_status = trainer.current_pokemon.status

        # You can format the status text however you like. Here's a simple example:
        status_text = small_font.render(f"Status: {pokemon_status}", True, (0, 0, 0))


        self.screen.blit(trainer_text, (x+20, y-40))
        self.screen.blit(pokemon_text, (x, y))
        self.screen.blit(hp_text, (x+20, y + 66))
        self.screen.blit(exp_text, (x+2, y + 97))
        # Display the status text under the EXP bar
        self.screen.blit(status_text, (x+2, y + 112))  # Adjust the y-coordinate as needed

    def load_resources(self):
        bg_image = pygame.image.load('pokemon_arena.jpg')
        
        # Get the original size
        original_width, original_height = bg_image.get_size()
        
        # Increase the size by 20%
        new_width = int(original_width * 1.5)
        new_height = int(original_height * 1.5)
        
        # Apply the new size
        bg_image = pygame.transform.scale(bg_image, (new_width, new_height))
        
        # Assuming the 'extract_and_save_gif_frames' function saves frames and returns their paths
        gif_frames = extract_and_save_gif_frames('anim_leaves.gif', 'frames')
        gif_images = [pygame.image.load(frame) for frame in gif_frames]
        gif_images_middle = [pygame.transform.scale(image, (image.get_width()*3, image.get_height()*3)) for image in gif_images]
        gif_images_top = [pygame.transform.flip(image, True, True) for image in gif_images[::-1]]
        
        return bg_image, gif_images, gif_images_middle, gif_images_top

    def update_display(self):
        # Clear the screen
        self.screen.fill((255, 255, 255))

        # Get screen size
        screen_width, screen_height = self.screen.get_size()

        # Get the size of the scaled background image
        bg_width, bg_height = self.bg_image.get_size()

        # Calculate the offset to center the background image
        bg_x_offset = (bg_width - screen_width) // 2
        bg_y_offset = (bg_height - screen_height) // 2

        # Blit the centered background
        self.screen.blit(self.bg_image, (-bg_x_offset, -bg_y_offset))

        # Increment the frame counter
        self.frame_counter += 1


        # Update GIF frames and blit them if the frame counter reaches the update rate
        if self.frame_counter >= self.frame_update_rate:
            self.current_frame_original = (self.current_frame_original + 1) % len(self.gif_images)
            self.current_frame_middle = (self.current_frame_middle + 1) % len(self.gif_images_middle)
            self.current_frame_top = (self.current_frame_top + 1) % len(self.gif_images_top)
            self.frame_counter = 0  # Reset the frame counter

        #self.screen.blit(self.gif_images[self.current_frame_original], (800, 600))
        #self.screen.blit(self.gif_images_middle[self.current_frame_middle], (0, 0))  # Centered middle gif
        #self.screen.blit(self.gif_images_top[self.current_frame_top], (0, 0))


        self.display_pokemon(self.trainer1, 100, 50)
        self.display_pokemon(self.trainer2, 880, 50)
        
        # Display the action buttons using the draw method
        offset = self.scroll_offset if self.show_scrollbar else 0
        for button in self.buttons:
            button.draw(self.screen, offset)

        

        if self.show_scrollbar:
            # Calculate the maximum scrollbar position
            max_scrollbar_y = self.BASE_HEIGHT - self.scrollbar_height
            total_possible_offset = (len(self.trainer1.items) * 60) - self.BASE_HEIGHT
            if total_possible_offset > 0:
                self.scrollbar_y = (self.scroll_offset / total_possible_offset) * max_scrollbar_y

            # Draw the scrollbar
            pygame.draw.rect(self.screen, (100, 100, 100), (775, self.scrollbar_y, 15, self.scrollbar_height))

        pygame.display.flip()

    def start(self):
        mouse_up = False
        done = False
        using_keyboard = False
        selected_button_index = 0

        num_buttons_per_row = 3  # Number of buttons per row
        num_rows = 2  # Number of rows

        while not done:
            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    done = True
                    pygame.quit()
                    return
                if event.type == pygame.MOUSEBUTTONUP:
                    mouse_up = True
                    using_keyboard = False  # Switch to mouse mode
                if event.type == pygame.MOUSEBUTTONDOWN and self.show_scrollbar:
                    # Scrollbar logic...
                    pass

                # Handle keyboard events
                if event.type == pygame.KEYDOWN:
                    using_keyboard = True  # Switch to keyboard mode
                    if event.key == pygame.K_DOWN:
                        selected_button_index = (selected_button_index + num_buttons_per_row) % len(self.buttons)
                    elif event.key == pygame.K_UP:
                        selected_button_index = (selected_button_index - num_buttons_per_row) % len(self.buttons)
                    elif event.key == pygame.K_LEFT:
                        if selected_button_index % num_buttons_per_row > 0:
                            selected_button_index -= 1
                    elif event.key == pygame.K_RIGHT:
                        if selected_button_index % num_buttons_per_row < num_buttons_per_row - 1:
                            selected_button_index += 1
                    elif event.key == pygame.K_RETURN:
                        selected_button = self.buttons[selected_button_index]
                        # Ensure the function is called with correct parameters
                        if selected_button.function:
                            if selected_button.params is not None:
                                selected_button.function(*selected_button.params)
                            else:
                                selected_button.function()

            # Update buttons based on mouse or keyboard interaction
            mouse_pos = pygame.mouse.get_pos()
            for i, button in enumerate(self.buttons):
                if using_keyboard:
                    button.highlighted = (i == selected_button_index)
                else:
                    button.update(mouse_pos, mouse_up)  # Update button state based on mouse interaction

            # Refresh the display
            self.update_display()
            self.clock.tick(30)
            mouse_up = False

def load_and_start(game_state):
    loaded_data = load_game_pygame(game_state)
    if loaded_data:
        game_state.update(loaded_data)  # Update the game state
        human_trainer = game_state['human_trainer']  # Extract the human_trainer from the game_state
        pre_battle_menu_pygame(pygame.display.get_surface(), game_state, human_trainer)

def load_last_and_start(game_state):
    loaded_data = load_last_game(game_state)
    if loaded_data:
        game_state.update(loaded_data)  # Update the game state
        human_trainer = game_state['human_trainer']  # Extract the human_trainer from the game_state
        pre_battle_menu_pygame(pygame.display.get_surface(), game_state, human_trainer)

def generate_random_pokemon_list(pokemons, moves, sample_size=50):
    """Generate a list of random Pokémon with adjusted levels and stats."""
    
    # Get a list of random Pokémon to choose from
    pokemon_list = random.sample(list(pokemons.values()), sample_size)

    leveled_pokemon_list = []
    for pokemon in pokemon_list:
        pokemon_copy = copy.deepcopy(pokemon)

        # Generate a level using a normal distribution centered around 30
        level = max(1, min(100, int(np.random.normal(loc=30, scale=7))))
        pokemon_copy.level = level

        # Adjust stats based on level and randomness
        pokemon_copy.max_health = int(pokemon.max_health * (level / 30) * random.uniform(0.8, 1.2))
        pokemon_copy.attack = int(pokemon.attack * (level / 30) * random.uniform(0.8, 1.2))
        pokemon_copy.defense = int(pokemon.defense * (level / 30) * random.uniform(0.8, 1.2))
        pokemon_copy.speed = int(pokemon.speed * (level / 30) * random.uniform(0.8, 1.2))
        pokemon_copy.current_health = pokemon_copy.max_health  # Set current health to max_health

        # Adjust price based on level
        pokemon_copy.price *= level

        # Get the last 4 moves that the Pokémon can learn at its current level
        pokemon_copy.moves = PokemonFactory.get_moves_at_level(pokemon_copy.moves_to_learn, pokemon_copy.level, moves)

        leveled_pokemon_list.append(pokemon_copy)

    return leveled_pokemon_list

def initialize_pygame():
    # Initialize pygame
    pygame.init()
    pygame.font.init()
    # Initialize the joystick module
    pygame.joystick.init()

    # Print the number of detected joysticks
    print(f"Number of joysticks detected: {pygame.joystick.get_count()}")

    # If there are any joysticks connected, set up the first one
    if pygame.joystick.get_count() > 0:
        joystick = pygame.joystick.Joystick(0)
        joystick.init()
    # Create a display window
    screen = pygame.display.set_mode((1280, 920), pygame.DOUBLEBUF)
    
    pygame.display.set_caption("Main Menu")

    
    # Get game state
    game_state = initialize_game()

    # Load the background image
    bg_image = pygame.image.load('pokemon_arena.jpg')
    bg_image = pygame.transform.scale(bg_image, (1280, 920))  # Scale the image to fit the screen
    

    # Extract required values from game_state
    trainers = game_state['trainers']
    human_trainer = game_state['human_trainer']
    pokemons = game_state['pokemons']
    items = game_state['items']
    tm_chart = game_state['tm_chart']
    spells_chart = game_state['spells_chart']
    #print(spells_chart)
    moves = game_state['moves']

    # Extract frames from the GIF and store them in a list
    gif_frames = extract_and_save_gif_frames('anim_leaves.gif', 'frames')
    gif_images = [pygame.image.load(frame) for frame in gif_frames]
    # Scale the frames of the middle GIF by 3 times
    gif_images_middle = [pygame.transform.scale(image, (image.get_width()*3, image.get_height()*3)) for image in gif_images]

    # Flip and reverse the frames for the top GIF
    gif_images_top = [pygame.transform.flip(image, True, True) for image in gif_images[::-1]]
    
    # Separate frame counters and current frame indices for each GIF
    current_frame_original = 0
    current_frame_middle = len(gif_images) // 3  # Starting from one-third of the way through
    current_frame_top = 2 * len(gif_images) // 3  # Starting from two-thirds of the way through
    frame_counter_original = 0
    frame_counter_middle = 0
    frame_counter_top = 0
    # Create buttons
    window_width, window_height = screen.get_size()
    button_width, button_height = 400, 100
    button_spacing = 20
    
    # Calculate total height occupied by all buttons including spacing
    total_button_height = (4 * button_height) + (3 * button_spacing)  # since there are 4 buttons

    # Calculate the starting y-position for the buttons
    start_y = (window_height - total_button_height) / 2

    # Create buttons with adjusted positions
    start_game_btn = Button((window_width - button_width) / 2, start_y, button_width, button_height, "NEW GAME", function=start_new_game_window, params=[game_state['trainers'], pokemons, items, tm_chart, spells_chart, moves])
    continue_game_btn = Button((window_width - button_width) / 2, start_y + button_height + button_spacing, button_width, button_height, "CONTINUE", function=load_last_and_start, params=[game_state])
    load_game_btn = Button((window_width - button_width) / 2, start_y + 2 * (button_height + button_spacing), button_width, button_height, "LOAD", function=load_game_pygame, params=[pygame.display.get_surface(), game_state])
    exit_game_btn = Button((window_width - button_width) / 2, start_y + 3 * (button_height + button_spacing), button_width, button_height, "EXIT", function=exit_game)
    update_game_btn = Button((window_width - button_width) / 2, start_y + 4 * (button_height + button_spacing), button_width, button_height, "UPDATE", function=launch_update_menu, params=[screen, bg_image])
    buttons = [start_game_btn, continue_game_btn, load_game_btn, exit_game_btn, update_game_btn]  # Add the new button to the list

    selected_button_index = 0  # Initialize selected_button_index here

    using_keyboard = False  # New variable to track the current input method

    # Game loop
    running = True
    frame_counter = 0
    while running:
        mouse_up = False
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            if event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True
                using_keyboard = False  # Set to False when the mouse is used
            if event.type == pygame.KEYDOWN:
                using_keyboard = True  # Set to True when the keyboard is used
                if event.key == pygame.K_DOWN:
                    selected_button_index = (selected_button_index + 1) % len(buttons)
                elif event.key == pygame.K_UP:
                    selected_button_index = (selected_button_index - 1) % len(buttons)
                elif event.key == pygame.K_RETURN:  # Handling the "Enter" key
                    buttons[selected_button_index].clicked = True
                    if buttons[selected_button_index].function:
                        if buttons[selected_button_index].params:
                            buttons[selected_button_index].function(*buttons[selected_button_index].params)
                        else:
                            buttons[selected_button_index].function()
                        # Handle joystick button presses
            if event.type == pygame.JOYBUTTONDOWN:
                print(f"Gamepad button {event.button} pressed")
                if event.button == 0:  # "A" button on most gamepads
                    buttons[selected_button_index].clicked = True
                    if buttons[selected_button_index].function:
                        if buttons[selected_button_index].params:
                            buttons[selected_button_index].function(*buttons[selected_button_index].params)
                        else:
                            buttons[selected_button_index].function()
                    
            # Handle joystick D-pad movements
            if event.type == pygame.JOYHATMOTION:
                hat_x, hat_y = event.value
                if hat_y == 1:  # D-pad up
                    selected_button_index = (selected_button_index - 1) % len(buttons)
                elif hat_y == -1:  # D-pad down
                    selected_button_index = (selected_button_index + 1) % len(buttons)

                   
        # Update which button is highlighted based on selection
        for i, button in enumerate(buttons):
            if i == selected_button_index:
                button.highlighted = True
            else:
                button.highlighted = False
        # Blit (draw) the background image first
        screen.blit(bg_image, (0, 0))

        #screen.fill((255, 255, 255))  # Fill the screen with white color

        # Display GIF frames at three different positions
        screen.blit(gif_images[current_frame_original], (800, 600))  # Original position
        screen.blit(gif_images_middle[current_frame_middle], (0, 0))  # Scaled position
        screen.blit(gif_images_top[current_frame_top], (0, 0))  # Flipped and reversed position
        
        frame_counter_original += 1
        frame_counter_middle += 1
        frame_counter_top += 1

        if frame_counter_original >= 2:  # Adjusted to play twice as fast
            current_frame_original = (current_frame_original + 1) % len(gif_images)
            frame_counter_original = 0
            
        if frame_counter_middle >= 2:  # Adjusted to play twice as fast
            current_frame_middle = (current_frame_middle + 1) % len(gif_images)
            frame_counter_middle = 0
            
        if frame_counter_top >= 2:  # Adjusted to play twice as fast
            current_frame_top = (current_frame_top + 1) % len(gif_images)
            frame_counter_top = 0

        # Update and draw buttons
        for button in buttons:
            button.update(pygame.mouse.get_pos(), mouse_up, keyboard_navigation=using_keyboard)
            button.draw(screen)

        pygame.display.flip()  # Update the display

        pygame.time.Clock().tick(60)  # Limit the frame rate to 60 FPS

    pygame.quit()

def extract_and_save_gif_frames(filename, target_dir):
    # Check if target directory exists, if not, create it
    if not os.path.exists(target_dir):
        os.makedirs(target_dir)
        
    with Image.open(filename) as img:
        frames = [frame.copy() for frame in ImageSequence.Iterator(img)]
        frame_files = []
        for i, frame in enumerate(frames):
            frame_file = os.path.join(target_dir, f'frame_{i}.png')
            frame.save(frame_file)
            frame_files.append(frame_file)
        return frame_files




def launch_update_menu(screen, bg_image):
    # Define button properties
    button_width, button_height = 400, 100
    button_spacing = 20
    window_width, window_height = screen.get_size()

    # Calculate the starting y-position for the buttons
    start_y = (window_height - 5 * button_height - 4 * button_spacing) / 2

    # Create update menu buttons
    update_csv_btn = Button((window_width - button_width) / 2, start_y, button_width, button_height, "UPDATE CSV", function=update_csv, params=[screen, bg_image])
    update_main_btn = Button((window_width - button_width) / 2, start_y + button_height + button_spacing, button_width, button_height, "UPDATE MAIN", function=update_main)
    update_art_btn = Button((window_width - button_width) / 2, start_y + 2 * (button_height + button_spacing), button_width, button_height, "UPDATE ART", function=update_art)
    update_maps_btn = Button((window_width - button_width) / 2, start_y + 3 * (button_height + button_spacing), button_width, button_height, "UPDATE MAPS", function=update_maps)
    update_all_btn = Button((window_width - button_width) / 2, start_y + 4 * (button_height + button_spacing), button_width, button_height, "UPDATE ALL", function=update_all)

    update_buttons = [update_csv_btn, update_main_btn, update_art_btn, update_maps_btn, update_all_btn]

    # Update menu loop
    running = True
    selected_button_index = 0
    while running:
        mouse_up = False
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            elif event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True
            elif event.type == pygame.KEYDOWN:
                if event.key == pygame.K_DOWN:
                    selected_button_index = (selected_button_index + 1) % len(update_buttons)
                elif event.key == pygame.K_UP:
                    selected_button_index = (selected_button_index - 1) % len(update_buttons)
                elif event.key == pygame.K_RETURN:
                    update_buttons[selected_button_index].clicked = True
                    update_buttons[selected_button_index].function()

        screen.blit(bg_image, (0, 0))  # Redraw background

        # Update and draw buttons
        for i, button in enumerate(update_buttons):
            button.highlighted = (i == selected_button_index)
            button.update(pygame.mouse.get_pos(), mouse_up)
            button.draw(screen)

        pygame.display.flip()
        pygame.time.Clock().tick(60)

def update_csv(screen, bg_image):
    launch_csv_update_menu(screen, bg_image)
    print("Updating CSV...")

def update_main():
    print("Updating Main...")

def update_art():
    print("Updating Art...")

def update_maps():
    print("Updating Maps...")

def update_all():
    print("Updating Everything...")


def launch_csv_update_menu(screen, bg_image):
    # Define button properties
    button_width, button_height = 400, 100
    button_spacing = 20
    window_width, window_height = screen.get_size()

    # Calculate the starting y-position for the buttons
    start_y = (window_height - 7 * button_height - 6 * button_spacing) / 2

    # Create buttons for the CSV update menu
    items_btn = Button((window_width - button_width) / 2, start_y, button_width, button_height, "ITEMS", function=update_items)
    moves_btn = Button((window_width - button_width) / 2, start_y + (button_height + button_spacing), button_width, button_height, "MOVES", function=update_moves)
    trainers_btn = Button((window_width - button_width) / 2, start_y + 2 * (button_height + button_spacing), button_width, button_height, "TRAINERS", function=update_trainers)
    pokemon_btn = Button((window_width - button_width) / 2, start_y + 3 * (button_height + button_spacing), button_width, button_height, "POKEMON", function=update_pokemon)
    locations_btn = Button((window_width - button_width) / 2, start_y + 4 * (button_height + button_spacing), button_width, button_height, "LOCATIONS", function=update_locations)
    spells_btn = Button((window_width - button_width) / 2, start_y + 5 * (button_height + button_spacing), button_width, button_height, "SPELLS", function=update_spells)
    tm_btn = Button((window_width - button_width) / 2, start_y + 6 * (button_height + button_spacing), button_width, button_height, "TM", function=update_tm)

    csv_update_buttons = [items_btn, moves_btn, trainers_btn, pokemon_btn, locations_btn, spells_btn, tm_btn]

    # CSV update menu loop
    running = True
    selected_button_index = 0
    while running:
        mouse_up = False
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            elif event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True
            elif event.type == pygame.KEYDOWN:
                if event.key == pygame.K_DOWN:
                    selected_button_index = (selected_button_index + 1) % len(csv_update_buttons)
                elif event.key == pygame.K_UP:
                    selected_button_index = (selected_button_index - 1) % len(csv_update_buttons)
                elif event.key == pygame.K_RETURN:
                    csv_update_buttons[selected_button_index].clicked = True
                    csv_update_buttons[selected_button_index].function()

        screen.blit(bg_image, (0, 0))  # Redraw background

        # Update and draw buttons
        for i, button in enumerate(csv_update_buttons):
            button.highlighted = (i == selected_button_index)
            button.update(pygame.mouse.get_pos(), mouse_up)
            button.draw(screen)

        pygame.display.flip()
        pygame.time.Clock().tick(60)

def update_csv_file(csv_filename):
    csv_url = f"https://raw.githubusercontent.com/mtusa1/PokePyPublic/main/csv/{csv_filename}"
    local_csv_path = csv_filename

    print(f"[DEBUG] Starting the update process for {csv_filename}")
    print(f"[DEBUG] Attempting to download from URL: {csv_url}")

    try:
        response = requests.get(csv_url)
        print(f"[DEBUG] Received response with status code: {response.status_code}")

        if response.status_code == 200:
            with open(local_csv_path, 'wb') as file:
                file.write(response.content)
            print(f"[DEBUG] {csv_filename} written to path: {local_csv_path}")
            print(f"{csv_filename} updated successfully.")
        else:
            print(f"[ERROR] Failed to download the CSV file. Status code: {response.status_code}")
    except Exception as e:
        print(f"[ERROR] An exception occurred: {e}")

# Update functions calling the generic function
def update_items():
    update_csv_file("items4.csv")

def update_moves():
    update_csv_file("moves5.csv")

def update_trainers():
    update_csv_file("trainers2.csv")

def update_pokemon():
    update_csv_file("pokemon7.csv")

def update_locations():
    update_csv_file("locations3.csv")

def update_spells():
    update_csv_file("spells.csv")

def update_tm():
    update_csv_file("tm.csv")


def start_new_game_window(trainers, pokemons, items, tm_chart, spells_chart, moves):
    pygame.init()
    screen = pygame.display.set_mode((1280, 920), pygame.DOUBLEBUF)
    pygame.display.set_caption("START NEW GAME")
    clock = pygame.time.Clock()

    # Load resources (background and GIFs)
    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()
    
    # Initialize the frame counters
    current_frame_original, current_frame_middle, current_frame_top = 0, 0, 0

    input_font = pygame.font.Font(font_path, 12)
    label_font = pygame.font.Font(font_path, 24)
    button_font = pygame.font.Font(font_path, 24)

    # Screen center calculation
    screen_center_x = screen.get_width() // 2

    # Input and button dimensions
    input_width = 400
    input_height = 32
    button_width = 200
    button_height = 100

    # Initialize cursor visibility and timer
    cursor_visible = True  # Cursor starts as visible
    cursor_switch_timedelta = 500  # Time in milliseconds to switch the cursor visibility
    last_switch_time = pygame.time.get_ticks()
    
    # Teal background properties
    background_color = (0, 128, 128)  # Teal color
    background_opacity = 191  # 75% opacity (255 * 0.75)
    border_color = (255, 255, 255)  # White color for the border
    border_radius = 10  # Rounded corner radius
    padding = 10  # Padding between the inputs and the background

    # Create a surface for the background with per-pixel alpha
    background_surface = pygame.Surface((input_width + 2 * padding, 3 * input_height + 30 * padding))
    background_surface.set_alpha(background_opacity)
    background_surface.fill(background_color)



    # Input fields centered on the screen
    """trainer_name_input = pygame.Rect(screen_center_x - input_width // 2, 300, input_width, input_height)
    trainer_name_text = ''
    trainer_name_label = label_font.render("NAME:", True, (255, 255, 255))

    trainer_region_input = pygame.Rect(screen_center_x - input_width // 2, 400, input_width, input_height)
    trainer_region_text = ''
    trainer_region_label = label_font.render("REGION:", True, (255, 255, 255))

    trainer_sub_region_input = pygame.Rect(screen_center_x - input_width // 2, 500, input_width, input_height)
    trainer_sub_region_text = ''
    trainer_sub_region_label = label_font.render("SUB-REGION:", True, (255, 255, 255))"""

    # Create InputBox instances
    trainer_name_input = InputBox(screen_center_x - input_width // 2, 300, input_width, input_height, input_font)
    trainer_region_input = InputBox(screen_center_x - input_width // 2, 400, input_width, input_height, input_font)
    trainer_sub_region_input = InputBox(screen_center_x - input_width // 2, 500, input_width, input_height, input_font)


    
    # Position for the background surface
    background_pos_x = trainer_name_input.rect.x - padding
    background_pos_y = trainer_name_input.rect.y - padding * 8

    
    # Centered Enter button
    #enter_button = pygame.Rect(screen_center_x - button_width // 2, 700, button_width, button_height)
    #enter_text = button_font.render('ENTER', True, (255, 255, 255))
    #enter_text_rect = enter_text.get_rect(center=enter_button.center)

    # Centered Enter button using Button class
    #enter_button_text = button_font.render('ENTER', True, (255, 255, 255))
    #enter_button = Button(screen_center_x - button_width // 2, 700, button_width, button_height, text=enter_button_text, function=exit_game)


    # Centered Enter button using Button class
    button_text = "ENTER"
    button_text_surface = button_font.render(button_text, True, (255, 255, 255))  # Render the text

    # Calculate the size of the text surface
    text_width, text_height = button_font.size(button_text)

    # Create a surface for the button with dimensions matching the button's size
    button_surface = pygame.Surface((button_width, button_height), pygame.SRCALPHA)

    # Blit the text surface onto the button surface, centering the text
    text_x = (button_width - text_width) // 2
    text_y = (button_height - text_height) // 2
    button_surface.blit(button_text_surface, (text_x, text_y))

    # Create the Enter button using the custom surface with centered text
    enter_button = Button(screen_center_x - button_width // 2, 700, button_width, button_height, text=button_surface, function=exit_game)



    color_active = pygame.Color('lightskyblue3')
    color_passive = pygame.Color('gray15')
    color_button = pygame.Color('dodgerblue2')

    # Default color settings for all input fields
    trainer_name_color = color_passive
    trainer_region_color = color_passive
    trainer_sub_region_color = color_passive

    active_input = None
    gif_frame_update_rate = 2  # Number of frames to wait before updating GIF frame
    frame_counter = 0  # Counter to track the number of frames since last GIF frame update




    done = False
    while not done:
        screen.fill((255, 255, 255))
        # Update mouse_pos outside the event loop
        mouse_pos = pygame.mouse.get_pos()
        mouse_up = False

        # Get the current time
        current_time = pygame.time.get_ticks()
        # Check if it's time to toggle the cursor visibility
        if current_time - last_switch_time >= cursor_switch_timedelta:
            cursor_visible = not cursor_visible
            last_switch_time = current_time
        

        # Create label surfaces
        trainer_name_label = label_font.render("NAME:", True, (255, 255, 255))
        trainer_region_label = label_font.render("REGION:", True, (255, 255, 255))
        trainer_sub_region_label = label_font.render("SUB-REGION:", True, (255, 255, 255))


        # Position for the background surface
        background_pos_x = trainer_name_input.rect.x - padding
        background_pos_y = trainer_name_input.rect.y - padding * 8

        # Adjust the labels' positions for centered alignment
        trainer_name_label_pos = (trainer_name_input.rect.x + (input_width // 2) - (trainer_name_label.get_width() // 2), trainer_name_input.rect.y - 75)
        trainer_region_label_pos = (trainer_region_input.rect.x + (input_width // 2) - (trainer_region_label.get_width() // 2), trainer_region_input.rect.y - 75)
        trainer_sub_region_label_pos = (trainer_sub_region_input.rect.x + (input_width // 2) - (trainer_sub_region_label.get_width() // 2), trainer_sub_region_input.rect.y - 75)

        # Increment the frame counter
        frame_counter += 1

        # Update GIF frames if the frame counter has reached the update rate
        # ... [previous code] ...

        # Update GIF frames if the frame counter has reached the update rate
        if frame_counter >= gif_frame_update_rate:
            if gif_images:  # Check if gif_images is not empty
                current_frame_original = (current_frame_original + 1) % len(gif_images)
            if gif_images_middle:  # Check if gif_images_middle is not empty
                current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
            if gif_images_top:  # Check if gif_images_top is not empty
                current_frame_top = (current_frame_top + 1) % len(gif_images_top)
            frame_counter = 0  # Reset the frame counter

        # Draw the background and GIFs
        screen.blit(bg_image, (0, 0))

        # Only blit the GIFs if the lists are not empty
        if gif_images:
            screen.blit(gif_images[current_frame_original], (800, 600))  # Adjust position as needed
        if gif_images_middle:
            screen.blit(gif_images_middle[current_frame_middle], (0, 0))  # Adjust position as needed
        if gif_images_top:
            screen.blit(gif_images_top[current_frame_top], (0, 0))  # Adjust position as needed

        # ... [rest of the code] ...


        # Draw the teal background with rounded corners
        screen.blit(background_surface, (background_pos_x, background_pos_y))
        pygame.draw.rect(screen, border_color, (background_pos_x, background_pos_y, input_width + 2 * padding, 3 * input_height + 30 * padding), 2, border_radius)

        

        #mouse_pos = (0, 0)
        #mouse_up = False

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                done = True

            mouse_pos = pygame.mouse.get_pos()
            mouse_up = event.type == pygame.MOUSEBUTTONUP

            # Handle events for each input box
            trainer_name_input.handle_event(event)
            trainer_region_input.handle_event(event)
            trainer_sub_region_input.handle_event(event)

            if event.type == pygame.MOUSEMOTION:
            # Update the button highlight based on mouse position
                enter_button.highlighted = enter_button.rect.collidepoint(mouse_pos)

            if event.type == pygame.MOUSEBUTTONDOWN:
                if trainer_name_input.rect.collidepoint(event.pos):
                    active_input = 'name'
                    color = color_active
                elif trainer_region_input.rect.collidepoint(event.pos):
                    active_input = 'region'
                    color = color_active
                elif trainer_sub_region_input.rect.collidepoint(event.pos):
                    active_input = 'sub_region'
                    color = color_active
                # Inside the "Enter" button event handler
                elif enter_button.rect.collidepoint(event.pos):
                    # Close the current window
                    pygame.quit()
                    human_trainer = Trainer(name=trainer_name_text, region=trainer_region_text, sub_region=trainer_sub_region_text)
                    
                    # Launch the Pokémon selection window with the region and sub_region values
                    selected_pokemons = select_pokemon_window(trainers, pokemons, human_trainer, 100000, items, tm_chart, spells_chart, moves)
                    print(f"Selected Pokémon: {[p.name for p in selected_pokemons]}")
                    return  # Exit the function after selecting the Pokémon

                else:
                    active_input = None
                    color = color_passive
            
            if event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True


            # Key down events
            if event.type == pygame.KEYDOWN:
                # Handling the tab key for switching input fields
                if event.key == pygame.K_TAB or event.key == pygame.K_DOWN:
                    if active_input == 'name':
                        active_input = 'region'
                        trainer_name_input.set_active(False)
                        trainer_region_input.set_active(True)
                    elif active_input == 'region':
                        active_input = 'sub_region'
                        trainer_region_input.set_active(False)
                        trainer_sub_region_input.set_active(True)
                    else:
                        active_input = 'name'
                        trainer_sub_region_input.set_active(False)
                        trainer_name_input.set_active(True)

                # Handling the up arrow key for switching input fields upwards
                elif event.key == pygame.K_UP:
                    if active_input == 'sub_region':
                        active_input = 'region'
                        trainer_sub_region_input.set_active(False)
                        trainer_region_input.set_active(True)
                    elif active_input == 'region':
                        active_input = 'name'
                        trainer_region_input.set_active(False)
                        trainer_name_input.set_active(True)
                    elif active_input == 'name':
                        active_input = 'sub_region'
                        trainer_name_input.set_active(False)
                        trainer_sub_region_input.set_active(True)

                # Handling other key events based on active input
                elif active_input == 'name':
                    if event.key == pygame.K_BACKSPACE:
                        trainer_name_text = trainer_name_text[:-1]
                    elif event.key == pygame.K_RETURN:
                        # Close the current window
                        pygame.quit()
                        human_trainer = Trainer(name=trainer_name_text, region=trainer_region_text, sub_region=trainer_sub_region_text)
                        # Launch the Pokémon selection window
                        selected_pokemons = select_pokemon_window(trainers, pokemons, human_trainer, 100000, items, tm_chart, spells_chart, moves)
                        print(f"Selected Pokémon: {[p.name for p in selected_pokemons]}")
                        return  # Exit the function after selecting the Pokémon
                    else:
                        trainer_name_text += event.unicode
                elif active_input == 'region':
                    if event.key == pygame.K_BACKSPACE:
                        trainer_region_text = trainer_region_text[:-1]
                    elif event.key == pygame.K_RETURN:
                        # Close the current window
                        pygame.quit()
                        human_trainer = Trainer(name=trainer_name_text, region=trainer_region_text, sub_region=trainer_sub_region_text)
                        # Launch the Pokémon selection window
                        selected_pokemons = select_pokemon_window(trainers, pokemons, human_trainer, 100000, items, tm_chart, spells_chart, moves)
                        print(f"Selected Pokémon: {[p.name for p in selected_pokemons]}")
                        return  # Exit the function after selecting the Pokémon                    
                    else:
                        trainer_region_text += event.unicode
                elif active_input == 'sub_region':
                    if event.key == pygame.K_BACKSPACE:
                        trainer_sub_region_text = trainer_sub_region_text[:-1]
                    # Handling the "Enter" key press
                    elif event.key == pygame.K_RETURN:
                        # Close the current window
                        pygame.quit()
                        human_trainer = Trainer(name=trainer_name_text, region=trainer_region_text, sub_region=trainer_sub_region_text)
                        # Launch the Pokémon selection window
                        selected_pokemons = select_pokemon_window(trainers, pokemons, human_trainer, 100000, items, tm_chart, spells_chart, moves)
                        print(f"Selected Pokémon: {[p.name for p in selected_pokemons]}")
                        return  # Exit the function after selecting the Pokémon
                    else:
                        trainer_sub_region_text += event.unicode
                
                # Handling the "Enter" key press
                elif event.key == pygame.K_RETURN:
                    # Close the current window
                    pygame.quit()
                    human_trainer = Trainer(name=trainer_name_text, region=trainer_region_text, sub_region=trainer_sub_region_text)
                    # Launch the Pokémon selection window
                    selected_pokemons = select_pokemon_window(trainers, pokemons, human_trainer, 100000, items, tm_chart, spells_chart, moves)
                    print(f"Selected Pokémon: {[p.name for p in selected_pokemons]}")
                    return  # Exit the function after selecting the Pokémon

        # Set the color of the active input field
        if active_input == 'name':
            trainer_name_color = color_active
        elif active_input == 'region':
            trainer_region_color = color_active
        elif active_input == 'sub_region':
            trainer_sub_region_color = color_active


        # Set the color of the active input field
        trainer_name_color = color_active if active_input == 'name' else color_passive
        trainer_region_color = color_active if active_input == 'region' else color_passive
        trainer_sub_region_color = color_active if active_input == 'sub_region' else color_passive



        # Fetch the current text from input boxes
        trainer_name_text = trainer_name_input.get_text()
        trainer_region_text = trainer_region_input.get_text()
        trainer_sub_region_text = trainer_sub_region_input.get_text()

        # Render the text
        """trainer_name_surface = input_font.render(trainer_name_text, True, (255, 255, 255))
        trainer_region_surface = input_font.render(trainer_region_text, True, (255, 255, 255))
        trainer_sub_region_surface = input_font.render(trainer_sub_region_text, True, (255, 255, 255))"""


        # Draw everything
        # Calculate the centered x position for the text within the input box
        #trainer_name_text_x_centered = trainer_name_input.rect.x + (trainer_name_input.rect.width - trainer_name_surface.get_width()) // 2
        #trainer_region_text_x_centered = trainer_region_input.rect.x + (trainer_region_input.rect.width - trainer_region_surface.get_width()) // 2
        #trainer_sub_region_text_x_centered = trainer_sub_region_input.rect.x + (trainer_sub_region_input.rect.width - trainer_sub_region_surface.get_width()) // 2



        # Draw the input boxes
        trainer_name_input.draw(screen)
        trainer_region_input.draw(screen)
        trainer_sub_region_input.draw(screen)

        # Draw the input fields with their respective colors
        screen.blit(trainer_name_label, trainer_name_label_pos)
        #screen.blit(trainer_name_surface, (trainer_name_text_x_centered, trainer_name_input.rect.y))
        pygame.draw.rect(screen, trainer_name_color, trainer_name_input.rect, 2)

        screen.blit(trainer_region_label, trainer_region_label_pos)
        #screen.blit(trainer_region_surface, (trainer_region_text_x_centered, trainer_region_input.rect.y))
        pygame.draw.rect(screen, trainer_region_color, trainer_region_input.rect, 2)

        screen.blit(trainer_sub_region_label, trainer_sub_region_label_pos)
        #screen.blit(trainer_sub_region_surface, (trainer_sub_region_text_x_centered, trainer_sub_region_input.rect.y))
        pygame.draw.rect(screen, trainer_sub_region_color, trainer_sub_region_input.rect, 2)





        # Calculate the centered x position for the text within the input box
        #trainer_name_text_x_centered = trainer_name_input.rect.x + (trainer_name_input.rect.width - trainer_name_surface.get_width()) // 2
        #trainer_region_text_x_centered = trainer_region_input.rect.x + (trainer_region_input.rect.width - trainer_region_surface.get_width()) // 2
        #trainer_sub_region_text_x_centered = trainer_sub_region_input.rect.x + (trainer_sub_region_input.rect.width - trainer_sub_region_surface.get_width()) // 2

        # Drawing the cursor for the active input if the cursor is visible
        if cursor_visible and active_input:
            active_input_box = trainer_name_input if active_input == 'name' else trainer_region_input if active_input == 'region' else trainer_sub_region_input
            if active_input_box.active:
                cursor_y = active_input_box.rect.y
                cursor_text = active_input_box.get_text()
                text_width, _ = input_font.size(cursor_text)
                cursor_x = active_input_box.rect.x + 5 + text_width  # Adjust the 5 if needed
                pygame.draw.line(screen, color_active, (cursor_x, cursor_y + 5), (cursor_x, cursor_y + input_height - 5), 2)



        # Drawing the Enter button
        #pygame.draw.rect(screen, color_button, enter_button)
        #screen.blit(enter_text, enter_text_rect)

        # Update and draw the enter button
        enter_button.update(mouse_pos, mouse_up)
        enter_button.draw(screen)

        pygame.display.flip()
        clock.tick(30)

    pygame.quit()

def select_pokemon_window(trainers, pokemons, human_trainer, trainer_coins, items, tm_chart, spells_chart, moves):
    # Initialize Pygame and set up the display
    pygame.init()
    screen = pygame.display.set_mode((1280, 920), pygame.DOUBLEBUF)
    pygame.display.set_caption("Select Your Pokémon")
    clock = pygame.time.Clock()

    # Load resources like images and fonts
    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()
    font = pygame.font.Font(font_path, 20)
    header_font = pygame.font.Font(font_path, 24)
    small_font = pygame.font.Font(font_path, 18)

    # Initialize frame counters for animation
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
    frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0

    # Initialize game state and other necessary variables
    game_state = initialize_game()
    initial_trainer_coins = trainer_coins
    pokemon_list = generate_random_pokemon_list(pokemons, moves)
    pokemon_buttons = [PokemonButton(120, 100 + i*100, 600, 75, pokemon, game_state) for i, pokemon in enumerate(pokemon_list)]
    selected_pokemons = []
    selected_pokemon_buttons = []
    highlighted_pokemon_text = ""
    highlighted_pokemon_image = None
    highlighted_pokemon_info = None  # Initialize highlighted_pokemon_info here
    scrolling = False
    scroll_y = 0
    scrollbar = pygame.Rect(750, 100, 20, 50)  # Scrollbar configurations
    max_scroll = max(0, len(pokemon_list) * 100 - 450)  # Calculate the maximum scroll value
    scroll_ratio = 450 / float(len(pokemon_list) * 100)
    # Define mouse_up variable
    mouse_up = False
    # Define sub-functions (get_pokemon_image_path, draw_pokemon_buttons, etc.)
    # ...
    def get_pokemon_image_path(pokemon_name):
        """Return the path to the image for the given Pokémon."""
        pokemon_details = pokemons.get(pokemon_name)
        if pokemon_details:
            pokemon_index = pokemon_details.index
            formatted_index = f"{pokemon_index:04}"
            return os.path.join("pokemon_pics", f"{formatted_index}{pokemon_name}.png")
        raise ValueError(f"No Pokemon found with the name {pokemon_name}")

    def draw_pokemon_buttons(screen, pokemon_buttons, scroll_y):
        for pokemon_button in pokemon_buttons:
            adjusted_button = pokemon_button.rect.move(0, -scroll_y)
            if 100 <= adjusted_button.top <= 550:
                pokemon_button.draw(screen, -scroll_y)

    def draw_selected_pokemon(screen, selected_pokemons):
        bg_x = 20
        bg_y = 640
        # Create a teal background square with 75% opacity
        bg_rect = pygame.Rect(bg_x, bg_y, 1240, 225)  # Adjust size as needed
        bg_color = (0, 128, 128, 192)  # Teal color with 75% opacity
        bg_surface = pygame.Surface((bg_rect.width, bg_rect.height), pygame.SRCALPHA)
        pygame.draw.rect(bg_surface, bg_color, bg_surface.get_rect(), border_radius=20)
        screen.blit(bg_surface, bg_rect.topleft)

        # Draw a white border around the background square
        border_color = (255, 255, 255)
        pygame.draw.rect(screen, border_color, bg_rect, 2, border_radius=20)

        
        """Draw selected Pokémon in a grid layout at the bottom of the window."""
        base_x, base_y = 100, 680
        x_increment, y_increment = 400, 100  # Space between buttons

        for index, pokemon in enumerate(selected_pokemons):
            column = index % 3
            row = index // 3
            x = base_x + column * x_increment
            y = base_y + row * y_increment
            image_path = get_pokemon_image_path(pokemon.name)
            pokemon_image = pygame.image.load(image_path)
            pokemon_image = pygame.transform.scale(pokemon_image, (50, 50))
            screen.blit(pokemon_image, (x, y))
            selected_text = small_font.render(f"{pokemon.name.upper()} : {pokemon.level}", True, (255, 255, 255))
            screen.blit(selected_text, (x + 60, y))

    def confirmation_window(selected_pokemons, pokemon_list, bg_image, gif_images, gif_images_middle, gif_images_top, mouse_up):
        nonlocal trainer_coins, pokemon_buttons  # Include pokemon_buttons as nonlocal
        confirm = False


        continue_btn = Button(140, 650, 400, 100, "CONTINUE")
        select_again_btn = Button(760, 650, 400, 100, "REDRAFT")

        # Initialize the frame counters for the confirmation window
        current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
        frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0



        while not confirm:
            mouse_pos = pygame.mouse.get_pos()  # Get the current mouse position
            
            
            # Check if the mouse is over any PokemonButton
            for pokemon_button in pokemon_buttons:
                if pokemon_button.rect.move(0, -scroll_y).collidepoint(mouse_pos):
                    pokemon_button.highlighted = True
                else:
                    pokemon_button.highlighted = False

                pokemon_button.draw(screen, -scroll_y)  # Draw the button

            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    pygame.quit()
                    return

                if event.type == pygame.MOUSEBUTTONUP:
                    mouse_up = True
                    if continue_btn.rect.collidepoint(mouse_pos):
                        confirm = True

                    elif select_again_btn.rect.collidepoint(event.pos):
                        # Reset trainer_coins to 10% of initial value
                        trainer_coins = initial_trainer_coins - (initial_trainer_coins * 0.10)

                        # Update existing PokemonButton instances for the redraft
                        # Update existing PokemonButton instances for the redraft
                        for i, pokemon in enumerate(pokemon_list):
                            if i < len(pokemon_buttons):
                                # If PokemonButton.update() is similar to Button.update()
                                pokemon_buttons[i].update(mouse_pos, mouse_up)  # Pass mouse_pos and mouse_up
                            else:
                                # Create a new PokemonButton instance if needed
                                btn_rect = pygame.Rect(120, 100 + i*100, 600, 75)
                                pokemon_button = PokemonButton(btn_rect.x, btn_rect.y, btn_rect.width, btn_rect.height, pokemon, game_state)
                                pokemon_buttons.append(pokemon_button)

                        return False
                    
                    if event.type == pygame.MOUSEBUTTONUP or event.type == pygame.MOUSEBUTTONDOWN:
                        # Update mouse_up status based on the event
                        mouse_up = event.type == pygame.MOUSEBUTTONUP
                    
                    if event.type == pygame.MOUSEBUTTONDOWN:
                        mouse_up = False

                    # Update buttons with the new mouse_up status
                    # Update buttons with the new mouse_up status
                    continue_btn.update(mouse_pos, mouse_up)
                    select_again_btn.update(mouse_pos, mouse_up)


            # Check if the mouse is hovering over the buttons
            if continue_btn.rect.collidepoint(mouse_pos):
                continue_btn.highlighted = True  # Highlight the button
            else:
                continue_btn.highlighted = False  # Remove highlight

            if select_again_btn.rect.collidepoint(mouse_pos):
                select_again_btn.highlighted = True  # Highlight the button
            else:
                select_again_btn.highlighted = False  # Remove highlight

            

            screen.fill((255, 255, 255))

            
            # Update GIF frames for the confirmation window
            frame_counter_original += 1
            frame_counter_middle += 1
            frame_counter_top += 1
            if frame_counter_original % 2 == 0:
                current_frame_original = (current_frame_original + 1) % len(gif_images)
            if frame_counter_middle % 2 == 0:
                current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
            if frame_counter_top % 2 == 0:
                current_frame_top = (current_frame_top + 1) % len(gif_images_top)

            # Draw the background and GIFs for the confirmation window
            screen.blit(bg_image, (0, 0))
            screen.blit(gif_images[current_frame_original], (800, 600))  # Adjust position as needed
            screen.blit(gif_images_middle[current_frame_middle], (0, 0))  # Adjust position as needed
            screen.blit(gif_images_top[current_frame_top], (0, 0))  # Adjust position as needed

            
            bg_x = 20
            bg_y = 140
            # Create a teal background square with 75% opacity
            bg_rect = pygame.Rect(bg_x, bg_y, 1240, 475)  # Adjust size as needed
            bg_color = (0, 128, 128, 192)  # Teal color with 75% opacity
            bg_surface = pygame.Surface((bg_rect.width, bg_rect.height), pygame.SRCALPHA)
            pygame.draw.rect(bg_surface, bg_color, bg_surface.get_rect(), border_radius=20)
            screen.blit(bg_surface, bg_rect.topleft)

            # Draw a white border around the background square
            border_color = (255, 255, 255)
            pygame.draw.rect(screen, border_color, bg_rect, 2, border_radius=20)



            # Display the selected Pokémon (as you've done in the main loop)
            screen_width, screen_height = screen.get_size()  # Get screen dimensions
            base_x, base_y = 50, (screen_height - 400) // 2  # Center the grid
            x_increment, y_increment = 600, 100  # Increased space between buttons for larger images

            for index, pokemon in enumerate(selected_pokemons):
                column = index % 2
                row = index // 2
                x = base_x + column * x_increment
                y = base_y + row * y_increment

                image_path = get_pokemon_image_path(pokemon.name)
                pokemon_image = pygame.image.load(image_path)
                pokemon_image = pygame.transform.scale(pokemon_image, (100, 100))  # Scale the image
                screen.blit(pokemon_image, (x, y))

                # Render larger text
                selected_text = small_font.render(f"{pokemon.name.upper()} : {pokemon.level}", True, (255, 255, 255))
                selected_text = pygame.transform.scale(selected_text, (selected_text.get_width() * 2, selected_text.get_height() * 2))
                screen.blit(selected_text, (x + 110, y))  # Adjust text position


            continue_btn.draw(screen)
            select_again_btn.draw(screen)
            
            pygame.display.flip()
            clock.tick(30)
        
        return True

    # Additional sub-functions (handle_events, update_display) and main loop...

    def handle_events():
        nonlocal done, scrolling, scroll_y, selected_pokemons, trainer_coins, mouse_up
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                done = True
                return

            if event.type == pygame.MOUSEBUTTONDOWN:
                if event.button == 1:  # Left mouse button
                    if scrollbar.collidepoint(event.pos):
                        scrolling = True
                    else:
                        mouse_pos = pygame.mouse.get_pos()
                        adjusted_mouse_pos = (mouse_pos[0], mouse_pos[1] + scroll_y)
                        deselected = handle_deselection(mouse_pos)
                        if not deselected:
                            handle_selection(adjusted_mouse_pos)

                elif event.button == 4:  # Mouse wheel scrolled up
                    scroll_y = max(scroll_y - 20, 0)
                elif event.button == 5:  # Mouse wheel scrolled down
                    scroll_y = min(scroll_y + 20, max_scroll)

            if event.type == pygame.MOUSEBUTTONUP and event.button == 1:
                mouse_up = True
                if scrolling:
                    scrolling = False

            if event.type == pygame.MOUSEMOTION:
                if scrolling:
                    scrollbar.move_ip(0, event.rel[1])
                    scrollbar.y = max(min(scrollbar.y, 550 - scrollbar.height), 100)
                    scroll_y = (scrollbar.y - 100) / (450 - scrollbar.height) * max_scroll
                else:
                    mouse_pos = pygame.mouse.get_pos()
                    highlight_pokemon_buttons(mouse_pos)

        # Update the position of the scrollbar based on scroll_y
        scrollbar.y = 100 + scroll_y / max_scroll * (450 - scrollbar.height)



    def update_display():
        screen.fill((255, 255, 255))
        screen.blit(bg_image, (0, 0))

        draw_pokemon_buttons(screen, pokemon_buttons, scroll_y)
        draw_selected_pokemon(screen, selected_pokemons)
        draw_header()
        pygame.draw.rect(screen, (255, 255, 255), scrollbar)

        # Display highlighted Pokémon info
        if highlighted_pokemon_info:
            name, price = highlighted_pokemon_info
            info_text = f"{name.upper()} - PRICE: {price}"
            info_render = small_font.render(info_text, True, (255, 255, 255))
            info_pos = (800, 100)  # Adjust position as needed
            screen.blit(info_render, info_pos)

            # Display a large image of the highlighted Pokémon under the label
            if highlighted_pokemon_image:
                image_pos = (info_pos[0], info_pos[1] + info_render.get_height() + 10)
                large_pokemon_image = pygame.transform.scale(highlighted_pokemon_image, (200, 200))  # Scale to a larger size
                screen.blit(large_pokemon_image, image_pos)

        pygame.display.flip()






    def handle_selection(adjusted_mouse_pos):
        nonlocal selected_pokemons, trainer_coins
        print("Handling selection...")
        for index, pokemon_button in enumerate(pokemon_buttons):
            if pokemon_button.rect.collidepoint(adjusted_mouse_pos) and len(selected_pokemons) < 6:
                selected_pokemons.append(pokemon_button.pokemon)
                trainer_coins -= pokemon_button.pokemon.price
                selected_pokemon_buttons.append(PokemonButton(120, 560 + len(selected_pokemons) * 50, 200, 50, pokemon_button.pokemon, game_state))
                pokemon_buttons.pop(index)
                # Re-adjust the y positions of the remaining buttons
                for i, remaining_button in enumerate(pokemon_buttons):
                    remaining_button.rect.y = 100 + i * 100
                return True
        return False



    def handle_deselection(mouse_pos):
        nonlocal selected_pokemons, trainer_coins
        print("Handling deselection...")
        for index, sel_pokemon_button in enumerate(selected_pokemon_buttons):
            print(f"Checking button {index} for deselection...")
            if sel_pokemon_button.rect.collidepoint(mouse_pos):
                print(f"Deselecting Pokemon: {selected_pokemons[index].name}")
                removed_pokemon = selected_pokemons.pop(index)
                selected_pokemon_buttons.pop(index)
                new_button = PokemonButton(120, 100 + len(pokemon_buttons) * 100, 600, 75, removed_pokemon, game_state)
                pokemon_buttons.append(new_button)
                pokemon_list.append(removed_pokemon)
                trainer_coins += removed_pokemon.price
                return True
        return False




    def highlight_pokemon_buttons(mouse_pos):
        global highlighted_pokemon_image, highlighted_pokemon_info
        for pokemon_button in pokemon_buttons:
            if pokemon_button.rect.move(0, -scroll_y).collidepoint(mouse_pos):
                pokemon_button.highlighted = True
                # Update the highlighted Pokemon image and info
                highlighted_pokemon_image_path = get_pokemon_image_path(pokemon_button.pokemon.name)
                highlighted_pokemon_image = pygame.image.load(highlighted_pokemon_image_path)
                highlighted_pokemon_image = pygame.transform.scale(highlighted_pokemon_image, (300, 300))
                highlighted_pokemon_info = (pokemon_button.pokemon.name, pokemon_button.pokemon.price)  # Store name and price
            else:
                pokemon_button.highlighted = False




    def draw_header():
        header_text = header_font.render(f"TRAINER: {human_trainer.name} | REGION: {human_trainer.region} | COINS: {trainer_coins}", True, (0, 0, 0))
        screen.blit(header_text, (50, 0))

    # Main loop and other code...
    # Main loop
    done = False
    # Main loop
    while not done:
        handle_events()
        update_display()


        # Draw the PokemonButtons
        #print("\nCurrent state of pokemon_buttons:")
        #for i, btn in enumerate(pokemon_buttons):
            #print(f"Button {i}: {btn.pokemon.name} at y position {btn.rect.y}")

        #print("\nCurrent state of selected_pokemons:")
        #for i, pkmn in enumerate(selected_pokemons):
            #print(f"Selected Pokemon {i}: {pkmn.name}")

        # Drawing the PokemonButtons
        #for i, pokemon_button in enumerate(pokemon_buttons):
            #pokemon_button.rect.y = 100 + i * 100 - scroll_y
            #if 100 <= pokemon_button.rect.y <= 550:
                #print(f"Drawing button {i} for Pokemon: {pokemon_button.pokemon.name}")
                #pokemon_button.draw(screen)       

        if len(selected_pokemons) == 6:
            print("Selected 6 Pokémon!")
            # Pass mouse_up to the confirmation window
            confirmation_result = confirmation_window(selected_pokemons, pokemon_list, bg_image, gif_images, gif_images_middle, gif_images_top, mouse_up)
            if not confirmation_result:
                # If the player chooses "SELECT AGAIN", reset the selected Pokémon and continue the main loop
                selected_pokemons.clear()
                continue

            # Update the human_trainer's pokemon_list and current_pokemon
            human_trainer.pokemon_list = selected_pokemons
            human_trainer.current_pokemon = selected_pokemons[0]
            human_trainer.coins = trainer_coins
            human_trainer.mana = 20
            human_trainer.max_mana = 20
            human_trainer.max_health = 20
            human_trainer.current_health = 20

            print("Human Trainer:", human_trainer)
            print(human_trainer.current_pokemon)
            print(human_trainer.pokemon_list)
            print(human_trainer.region)

            # Transition to the next game state or menu
            pre_battle_menu_pygame(screen, game_state, human_trainer)
            done = True

    pygame.quit()
    return selected_pokemons

"""def select_pokemon_window(trainers, pokemons, human_trainer, trainer_coins, items, tm_chart, spells_chart, moves):
    pygame.init()
    screen = pygame.display.set_mode((1280, 920))
    pygame.display.set_caption("Select Your Pokémon")
    clock = pygame.time.Clock()

    # Load resources (new)
    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()

    # Initialize the frame counters (new)
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
    frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0

    game_state = initialize_game()  # Ensure this is called before creating PokemonButton instances


    font = pygame.font.Font(font_path, 20)
    header_font = pygame.font.Font(font_path, 24)
    small_font = pygame.font.Font(font_path, 18)

    print(human_trainer.name)
    print(human_trainer.region)

    initial_trainer_coins = trainer_coins

    # Get a list of 50 random Pokémon to choose from
    pokemon_list = generate_random_pokemon_list(pokemons, moves)
    

    
    def get_pokemon_image_path(pokemon_name):
        #Return the path to the image for the given Pokémon.
        pokemon_names = list(pokemons.keys())  # Get list of Pokémon names
        pokemon_details = pokemons.get(pokemon_name)
        if not pokemon_details:
            raise ValueError(f"No Pokemon found with the name {pokemon_name}")

        try:
            pokemon_index = pokemon_details.index
            formatted_index = f"{pokemon_index:04}"  # Zero-pad the index to ensure it's 4 digits
        except ValueError:
            raise ValueError(f"No Pokemon found with the name {pokemon_name}")
                
        #return os.path.join("F:\\Scripts\\PokePyMain-main\\pokemon_pics", f"{formatted_index}{pokemon_name}.png")
        #return os.path.join("C:\\Users\\matth\\OneDrive\\PokePy\\PokePyMain-main\\pokemon_pics", f"{formatted_index}{pokemon_name}.png")
        #return os.path.join("C:\\Users\\Tusa\\OneDrive\\Documents\\PokePyMain-main\\pokemon_pics", f"{formatted_index}{pokemon_name}.png")
    
        return os.path.join("pokemon_pics", f"{formatted_index}{pokemon_name}.png")

    
    def confirmation_window(selected_pokemons, pokemon_list, bg_image, gif_images, gif_images_middle, gif_images_top):
        nonlocal trainer_coins, pokemon_buttons  # Include pokemon_buttons as nonlocal
        confirm = False
        continue_btn = Button(140, 650, 400, 100, "CONTINUE")
        select_again_btn = Button(760, 650, 400, 100, "REDRAFT")

        # Initialize the frame counters for the confirmation window
        current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
        frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0

        while not confirm:
            mouse_pos = pygame.mouse.get_pos()  # Get the current mouse position
            
            
            # Check if the mouse is over any PokemonButton
            for pokemon_button in pokemon_buttons:
                if pokemon_button.rect.move(0, -scroll_y).collidepoint(mouse_pos):
                    pokemon_button.highlighted = True
                else:
                    pokemon_button.highlighted = False

                pokemon_button.draw(screen, -scroll_y)  # Draw the button

            for event in pygame.event.get():
                if event.type == pygame.QUIT:
                    pygame.quit()
                    return

                if event.type == pygame.MOUSEBUTTONUP:

                    if continue_btn.rect.collidepoint(mouse_pos):
                        confirm = True

                    elif select_again_btn.rect.collidepoint(event.pos):
                        # Reset trainer_coins to 10% of initial value
                        trainer_coins = initial_trainer_coins - (initial_trainer_coins * 0.10)

                        # Update existing PokemonButton instances for the redraft
                        for i, pokemon in enumerate(pokemon_list):
                            if i < len(pokemon_buttons):
                                # Update the existing PokemonButton instance
                                pokemon_buttons[i].update(pokemon)
                            else:
                                # Create a new PokemonButton instance if needed
                                btn_rect = pygame.Rect(120, 100 + i*100, 600, 75)
                                pokemon_button = PokemonButton(btn_rect.x, btn_rect.y, btn_rect.width, btn_rect.height, pokemon, game_state)
                                pokemon_buttons.append(pokemon_button)

                        return False


            # Check if the mouse is hovering over the buttons
            if continue_btn.rect.collidepoint(mouse_pos):
                continue_btn.highlighted = True  # Highlight the button
            else:
                continue_btn.highlighted = False  # Remove highlight

            if select_again_btn.rect.collidepoint(mouse_pos):
                select_again_btn.highlighted = True  # Highlight the button
            else:
                select_again_btn.highlighted = False  # Remove highlight

            

            screen.fill((255, 255, 255))

            
            # Update GIF frames for the confirmation window
            frame_counter_original += 1
            frame_counter_middle += 1
            frame_counter_top += 1
            if frame_counter_original % 2 == 0:
                current_frame_original = (current_frame_original + 1) % len(gif_images)
            if frame_counter_middle % 2 == 0:
                current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
            if frame_counter_top % 2 == 0:
                current_frame_top = (current_frame_top + 1) % len(gif_images_top)

            # Draw the background and GIFs for the confirmation window
            screen.blit(bg_image, (0, 0))
            screen.blit(gif_images[current_frame_original], (800, 600))  # Adjust position as needed
            screen.blit(gif_images_middle[current_frame_middle], (0, 0))  # Adjust position as needed
            screen.blit(gif_images_top[current_frame_top], (0, 0))  # Adjust position as needed

            
            # Display the selected Pokémon (as you've done in the main loop)
            base_y = 100
            base_x = 100
            x_increment = 300
            y_increment = 50
            for i, pokemon in enumerate(selected_pokemons):
                current_x = base_x + (i % 2) * x_increment
                current_y = base_y + (i // 2) * y_increment
                selected_text = small_font.render(f"{pokemon.name.upper()} : {pokemon.level}", True, (255, 255, 255))
                selected_pokemon_image = pygame.image.load(get_pokemon_image_path(pokemon.name))
                scaled_pokemon_image = pygame.transform.scale(selected_pokemon_image, (50, 50))
                screen.blit(scaled_pokemon_image, (current_x, current_y))
                screen.blit(selected_text, (current_x + 60, current_y))

            continue_btn.draw(screen)
            select_again_btn.draw(screen)
            
            pygame.display.flip()
            clock.tick(30)
        
        return True

    # Scrollbar configurations
    scrollbar_width = 20
    scrollbar_height = 50  # Height of the scrollbar handle
    scrollbar = pygame.Rect(750, 100, scrollbar_width, scrollbar_height)  # Initial position and size

    # Calculate the maximum scroll based on the area above y = 550
    list_height = len(pokemon_list) * 100  # Total height of the list
    visible_height = 450  # Height of the area above the black line (550 - 100)
    max_scroll = max(0, list_height - visible_height)  # Calculate the maximum scroll value

    # Calculate the ratio of scrollbar movement to the total scrollable area
    scroll_ratio = visible_height / float(list_height)

    scrolling = False
    scroll_y = 0

    # Remove this section that creates the dictionary-based buttons
    # buttons = []
    # for i, pokemon in enumerate(pokemon_list):
    #     btn_rect = pygame.Rect(120, 100 + i*100, 600, 75) 
    #     btn_text = f"{pokemon.name.upper()} (LEVEL {pokemon.level}) - {pokemon.price} COINS"
    #     pokemon_image = pygame.image.load(get_pokemon_image_path(pokemon.name))
    #     button = {"rect": btn_rect, "text": btn_text, "pokemon": pokemon, "image": pokemon_image}
    #     buttons.append(button)


    # Create PokemonButton instances for each Pokémon
    pokemon_buttons = []
    for i, pokemon in enumerate(pokemon_list):
        btn_x = 120
        btn_y = 100 + i*100
        btn_width = 600
        btn_height = 75
        pokemon_button = PokemonButton(btn_x, btn_y, btn_width, btn_height, pokemon, game_state)
        pokemon_buttons.append(pokemon_button)

    selected_pokemons = []
    selected_indices = []  # Track indices of selected Pokémon

    # Before the main loop
    selected_pokemon_buttons = []  # To store buttons for selected Pokémon

    # Before the main loop
    highlighted_pokemon_text = ""
    highlighted_pokemon_image = None


    def handle_deselection(mouse_pos, selected_pokemons, selected_pokemon_buttons, pokemon_buttons, pokemon_list, trainer_coins):
        for index, sel_pokemon_button in enumerate(selected_pokemon_buttons):
            if sel_pokemon_button.rect.collidepoint(mouse_pos):
                print(f"Deselecting Pokémon: {selected_pokemons[index].name}")
                removed_pokemon = selected_pokemons.pop(index)
                selected_pokemon_buttons.pop(index)
                new_pokemon_button = PokemonButton(120, 100 + len(pokemon_buttons) * 100, 600, 75, removed_pokemon, game_state)
                pokemon_buttons.append(new_pokemon_button)
                pokemon_list.append(removed_pokemon)
                trainer_coins += removed_pokemon.price
                return True, trainer_coins
        return False, trainer_coins
    
    def handle_selection(adjusted_mouse_pos, selected_pokemons, selected_pokemon_buttons, pokemon_buttons, pokemon_list, trainer_coins):
        for index, pokemon_button in enumerate(pokemon_buttons):
            button_rect_adjusted = pokemon_button.rect.move(0, -scroll_y)
            if button_rect_adjusted.collidepoint(adjusted_mouse_pos) and len(selected_pokemons) < 6:

                print(f"Selecting Pokémon: {pokemon_button.pokemon.name} at index {index}")
                selected_pokemons.append(pokemon_button.pokemon)
                trainer_coins -= pokemon_button.pokemon.price
                selected_pokemon_buttons.append(PokemonButton(120, 560 + len(selected_pokemons) * 50, 200, 50, pokemon_button.pokemon, game_state))
                pokemon_buttons.pop(index)
                for pkmn_index, pkmn in enumerate(pokemon_list):
                    if pkmn.name == pokemon_button.pokemon.name:
                        pokemon_list.pop(pkmn_index)
                        break
                return True, trainer_coins
        return False, trainer_coins



    game_state = initialize_game()

    done = False
    mouse_up = False  # Add this line to initialize mouse_up

    while not done:
        screen.fill((255, 255, 255))  # You might want to remove this if the background image covers the whole screen

        # Initialize click_processed at the start of each iteration
        click_processed = False

        # Update GIF frames (new)
        frame_counter_original += 1
        frame_counter_middle += 1
        frame_counter_top += 1
        if frame_counter_original % 2 == 0:
            current_frame_original = (current_frame_original + 1) % len(gif_images)
        if frame_counter_middle % 2 == 0:
            current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        if frame_counter_top % 2 == 0:
            current_frame_top = (current_frame_top + 1) % len(gif_images_top)

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                done = True

            if event.type == pygame.MOUSEBUTTONUP:
                mouse_up_pos = pygame.mouse.get_pos()
                adjusted_mouse_up_pos = (mouse_up_pos[0], mouse_up_pos[1] + scroll_y)

                deselected, trainer_coins = handle_deselection(mouse_up_pos, selected_pokemons, selected_pokemon_buttons, pokemon_buttons, pokemon_list, trainer_coins)
                if deselected:
                    continue

                selected, trainer_coins = handle_selection(adjusted_mouse_up_pos, selected_pokemons, selected_pokemon_buttons, pokemon_buttons, pokemon_list, trainer_coins)
                if selected:
                    continue

                scrolling = False

                # Debug: Print current state of Pokémon lists after selection/deselection
                print("\nCurrent Pokémon List:")
                for idx, pkmn in enumerate(pokemon_list):
                    print(f"{idx+1}: {pkmn.name}")

                print("\nSelected Pokémon List:")
                for idx, selected_pkmn in enumerate(selected_pokemons):
                    print(f"{idx+1}: {selected_pkmn.name}")

                # Update positions of pokemon_buttons
                for i, pokemon_button in enumerate(pokemon_buttons):
                    pokemon_button.rect.y = 100 + i * 100
                    pokemon_list[i] = pokemon_button.pokemon


                if scrollbar.collidepoint(event.pos):
                    scrolling = True
                elif event.button == 4:  # Mouse wheel scrolled up
                    scroll_step = 10 * scroll_ratio  # Adjust the scroll step based on the ratio
                    scrollbar.y = max(scrollbar.y - scroll_step, 100)
                    scroll_y = max(scroll_y - (scroll_step / scroll_ratio), 0)
                elif event.button == 5:  # Mouse wheel scrolled down
                    scroll_step = 10 * scroll_ratio  # Adjust the scroll step based on the ratio
                    scrollbar.y = min(scrollbar.y + scroll_step, 550 - scrollbar.height)
                    scroll_y = min(scroll_y + (scroll_step / scroll_ratio), max_scroll)


                # Add a condition to ensure normal button clicks are not from mouse wheel
                elif event.button in [1, 2, 3]:  # Left, middle, right mouse button
                    adjusted_mouse_pos = (event.pos[0], event.pos[1] + scroll_y)

                    # Pokémon selection logic
                    for index, pokemon_button in enumerate(pokemon_buttons):
                        if pokemon_button.rect.collidepoint(adjusted_mouse_pos) and len(selected_pokemons) < 6:
                            selected_pokemons.append(pokemon_button.pokemon)
                            trainer_coins -= pokemon_button.pokemon.price
                            pokemon_buttons.pop(index)
                            break



                else:
                    # Handling selection and deselection of Pokémon
                    adjusted_mouse_pos = (event.pos[0], event.pos[1] + scroll_y)
                    for index, pokemon_button in enumerate(pokemon_buttons):
                        if pokemon_button.rect.collidepoint(adjusted_mouse_pos) and len(selected_pokemons) < 6:
                            selected_pokemons.append(pokemon_button.pokemon)
                            selected_pokemon_buttons.append(PokemonButton(120, 560 + len(selected_pokemons) * 50, 200, 50, pokemon_button.pokemon, game_state))
                            trainer_coins -= pokemon_button.pokemon.price
                            pokemon_buttons.pop(index)
                            break

                    for index, sel_pokemon_button in enumerate(selected_pokemon_buttons):
                        if sel_pokemon_button.rect.collidepoint(event.pos):
                            # Remove this Pokémon from selected and add it back to the list
                            removed_pokemon = selected_pokemons.pop(index)
                            selected_pokemon_buttons.pop(index)
                            new_pokemon_button = PokemonButton(120, 100 + len(pokemon_buttons) * 100, 600, 75, removed_pokemon, game_state)
                            pokemon_buttons.append(new_pokemon_button)
                            pokemon_list.append(removed_pokemon)  # Also add back to the pokemon_list
                            trainer_coins += removed_pokemon.price
                            break



            if event.type == pygame.MOUSEMOTION:
                mouse_pos = pygame.mouse.get_pos()
                for pokemon_button in pokemon_buttons:
                    if pokemon_button.rect.move(0, -scroll_y).collidepoint(mouse_pos):
                        pokemon_button.highlighted = True
                        # Update the text for the highlighted Pokémon
                        highlighted_pokemon_text = f"{pokemon_button.pokemon.name.upper()} (LEVEL {pokemon_button.pokemon.level}) - {pokemon_button.pokemon.price} COINS"
                    else:
                        pokemon_button.highlighted = False

            # Draw the PokemonButtons after updating their highlighted status
            for pokemon_button in pokemon_buttons:
                adjusted_button = pokemon_button.rect.move(0, -scroll_y)
                if 100 <= adjusted_button.top <= 550 and adjusted_button.bottom <= 550:
                    pokemon_button.draw(screen, -scroll_y)

            if event.type == pygame.MOUSEBUTTONDOWN:
                if scrollbar.collidepoint(event.pos):
                    scrolling = True

            if event.type == pygame.MOUSEBUTTONUP:
                scrolling = False

            if event.type == pygame.MOUSEMOTION and scrolling:
                scrollbar.move_ip(0, event.rel[1])
                scrollbar.y = max(min(scrollbar.y, 550 - scrollbar.height), 100)
                scroll_y = (scrollbar.y - 100) / (450 - scrollbar.height) * max_scroll


        # Draw the background and GIFs (new)
        screen.blit(bg_image, (0, 0))
        screen.blit(gif_images[current_frame_original], (800, 600))  # Adjust position as needed
        screen.blit(gif_images_middle[current_frame_middle], (0, 0))  # Adjust position as needed
        screen.blit(gif_images_top[current_frame_top], (0, 0))  # Adjust position as needed

        # Display header
        header_text = header_font.render(f"TRAINER: {human_trainer.name} | REGION: {human_trainer.region} | COINS: {trainer_coins}", True, (0, 0, 0))
        screen.blit(header_text, (50, 0))

        # Draw the scrollbar
        pygame.draw.rect(screen, (255, 255, 255), scrollbar)
        
        # Replace the existing drawing logic with drawing of PokemonButton instances
        # Drawing the PokemonButtons
        #for pokemon_button in pokemon_buttons:
        #    adjusted_button = pokemon_button.rect.move(0, -scroll_y)
        #    if 100 <= adjusted_button.top <= 550 and adjusted_button.bottom <= 550:
        #        pokemon_button.draw(screen, -scroll_y)

        #        btn_text = font.render(button["text"], True, (255, 255, 255))
        #        screen.blit(btn_text, (750, 5))

        # Draw the PokemonButtons after updating their highlighted status
        # Draw the PokemonButtons after updating their highlighted status
        # Drawing the PokemonButtons and their labels
        # Drawing the PokemonButtons and their labels
        # Drawing the PokemonButtons and their labels
        for i, pokemon_button in enumerate(pokemon_buttons):
            pokemon_button.rect.y = 100 + i * 100
            adjusted_button = pokemon_button.rect.move(0, -scroll_y)
            if 100 <= adjusted_button.top <= 550 and adjusted_button.bottom <= 550:
                pokemon_button.draw(screen, -scroll_y)

                # The position number is directly based on the index in the pokemon_list
                position_number = i + 1  # "+ 1" to start numbering from 1 instead of 0
                label_text = font.render(str(position_number), True, (0, 0, 0))
                label_x = btn_x - 30  # Adjust as needed to position the label to the left of the button
                label_y = adjusted_button.y
                screen.blit(label_text, (label_x, label_y))

                if pokemon_button.highlighted:
                    # Update the text for the highlighted Pokémon
                    highlighted_pokemon_text = f"{pokemon_button.pokemon.name.upper()} (LEVEL {pokemon_button.pokemon.level}) - {pokemon_button.pokemon.price} COINS"
                    # Load and scale the image of the highlighted Pokémon
                    highlighted_pokemon_image_path = get_pokemon_image_path(pokemon_button.pokemon.name)
                    highlighted_pokemon_image = pygame.image.load(highlighted_pokemon_image_path)
                    highlighted_pokemon_image = pygame.transform.scale(highlighted_pokemon_image, (400, 400))  # Adjust size as needed


        # Draw the highlighted pokemon text and image
        if highlighted_pokemon_text:
            btn_text_surface = font.render(highlighted_pokemon_text, True, (255, 255, 255))
            screen.blit(btn_text_surface, (750, 5))  # Adjust the position as needed

            if highlighted_pokemon_image:
                # Draw the highlighted pokemon image
                screen.blit(highlighted_pokemon_image, (825, 75))  # Adjust the position as needed

  


        # Display a line separating the list from the selected Pokémon
        pygame.draw.line(screen, (0, 0, 0), (0, 550), (950, 550))

        # Draw selected Pokémon buttons
        base_x = 100
        base_y = 560
        x_increment = 300
        for index, pokemon in enumerate(selected_pokemons):
            if index >= len(selected_pokemon_buttons):
                # Create a new button for this selected Pokémon
                btn_x = base_x + (index % 2) * x_increment
                btn_y = base_y + (index // 2) * 50
                sel_pokemon_button = PokemonButton(btn_x, btn_y, 200, 50, pokemon, game_state)
                selected_pokemon_buttons.append(sel_pokemon_button)
            selected_pokemon_buttons[index].draw(screen)

        # Display selected Pokémon below the line
        # base_y = 560
        # base_x = 100
        # x_increment = 300  # Set this based on how much space you want between columns
        # y_increment = 50   # Space between rows
        # for i, pokemon in enumerate(selected_pokemons):
        #     current_x = base_x + (i % 2) * x_increment
        #     current_y = base_y + (i // 2) * y_increment

        #     selected_text = small_font.render(f"{pokemon.name.upper()} : {pokemon.level}", True, (255, 255, 255))
            
            # Load and display the image of the selected Pokémon
        #     selected_pokemon_image = pygame.image.load(get_pokemon_image_path(pokemon.name))
        #     scaled_pokemon_image = pygame.transform.scale(selected_pokemon_image, (50, 50))
        #     screen.blit(scaled_pokemon_image, (current_x, current_y))
            
            # Display the name of the selected Pokémon to the right of its image
        #     screen.blit(selected_text, (current_x + 60, current_y))


        # Exit when 6 Pokémon are selected
        if len(selected_pokemons) == 6:
            print("Selected 6 Pokémon!")
            # Show confirmation window with the background and GIFs
            if not confirmation_window(selected_pokemons, pokemon_list, bg_image, gif_images, gif_images_middle, gif_images_top):
                # If the player chooses "SELECT AGAIN", reset the selected Pokémon and continue the main loop
                selected_pokemons.clear()
                continue
            
            # Update the human_trainer's pokemon_list and current_pokemon
            human_trainer.pokemon_list = selected_pokemons
            human_trainer.current_pokemon = selected_pokemons[0]
            human_trainer.coins = trainer_coins
            human_trainer.mana = 20
            human_trainer.max_mana = 20
            human_trainer.max_health = 20
            human_trainer.current_health = 20

            print("Human Trainer:", human_trainer)
            print(human_trainer.current_pokemon)
            print(human_trainer.pokemon_list)
            print(human_trainer.region)
            
            # You can add any logic here like transition to the next game state or menu
            pre_battle_menu_pygame(screen, game_state, human_trainer)
            done = True

        pygame.display.flip()
        clock.tick(30)

    pygame.quit()
    return selected_pokemons

    # You can call this function to start the selection process
    # selected_pokemons = select_pokemon_window(trainers, pokemons, "Ash", 100000, items, tm_chart, spells_chart, moves)
"""

def load_selected_game(save_file, game_state, screen):
    try:
        loaded_data = load_game_from_file(save_file, game_state)  
        if loaded_data:
            game_state.update(loaded_data)  
            human_trainer = game_state['human_trainer']  # Extract the human_trainer from the game_state
            pre_battle_menu_pygame(screen, game_state, human_trainer)
    except ValueError as e:
        print(e)

def create_load_game_buttons(screen, screen_width, screen_height, saves, game_state):
    button_width, button_height = 700, 100
    button_spacing = 20

    buttons = []
    for idx, save in enumerate(saves):
        btn = Button((screen_width - button_width) / 2, 0, button_width, button_height, save, function=load_selected_game, params=[save, game_state, screen])
        buttons.append(btn)

    return buttons

def load_game_pygame(screen, game_state):
    # Define the button dimensions and spacing again for use in this function
    button_height = 100
    button_spacing = 20

    # Padding constants
    top_padding = 200
    bottom_padding = 200

    saves = get_save_files()
    if not saves:
        print("No saved games found.")
        return game_state

    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()
    window_width, window_height = screen.get_size()
    buttons = create_load_game_buttons(screen, window_width, window_height, saves, game_state)

    # Create the BACK button
    button_width, button_height = 200, 100
    back_btn_x = 20  # Left margin
    back_btn_y = window_height - button_height - 20  # 20 pixels above the bottom of the window
    back_btn = Button(back_btn_x, back_btn_y, button_width, button_height, "BACK", function=pre_battle_menu_pygame, params=[screen, game_state, game_state['human_trainer']])

    # Initialize scrollbar
    total_saves_height = len(saves) * (button_height + button_spacing)
    scrollbar = Scrollbar(window_width - 130, 100, 40, 700, 100, total_saves_height)
    scrollbar_dragging = False

    # Initialize frame counters
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
    frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0

    def adjust_scrollbar(scrollbar, target_offset, total_height, window_height):
        # Calculate the percentage position for the scrollbar
        max_scroll = total_height - window_height
        percentage = min(max(target_offset / max_scroll, 0), 1)
        scrollbar.handle_y = scrollbar.y + percentage * (scrollbar.height - scrollbar.handle_height)

    selected_button_index = 0  # Initialize with the first button selected
    using_keyboard = False
    visible_buttons_count = 4  # Adjust this based on the number of buttons visible at a time

    running = True
    while running:
        # Clear the screen at the start of each frame
        screen.fill((0, 0, 0))  # Clear with background color
        screen.blit(bg_image, (0, 0))

        # Update and draw GIF images
        screen.blit(gif_images[current_frame_original], (0, 0))
        screen.blit(gif_images_middle[current_frame_middle], (0, 0))
        screen.blit(gif_images_top[current_frame_top], (0, 0))

        # Handle all events in a single loop
        mouse_up = False
        mouse_moved = False
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            elif event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True
                scrollbar_dragging = False
                if back_btn.rect.collidepoint(event.pos):
                    back_btn.clicked = True
                    if back_btn.function:
                        back_btn.function(*back_btn.params if back_btn.params else [])
                else:
                    for idx, button in enumerate(buttons):
                        if button.rect.collidepoint(event.pos):
                            button.clicked = True
                            if button.function:
                                button.function(*button.params if button.params else [])
                            selected_button_index = idx  # Update index based on mouse click
                            using_keyboard = False  # Disable keyboard navigation when mouse is used

            elif event.type == pygame.MOUSEBUTTONDOWN:
                if scrollbar.is_over_handle(event.pos):
                    scrollbar_dragging = True
                    mouse_y_offset = event.pos[1] - scrollbar.handle_y

            elif event.type == pygame.MOUSEMOTION:
                mouse_moved = True
                if scrollbar_dragging:
                    new_handle_y = event.pos[1] - mouse_y_offset
                    scrollbar.move_handle(new_handle_y - scrollbar.handle_y)
                else:
                    for idx, button in enumerate(buttons):
                        if button.rect.collidepoint(event.pos):
                            selected_button_index = idx  # Update index based on mouse movement
                            using_keyboard = False  # Disable keyboard navigation when mouse is used

            # Handle keyboard navigation
            elif event.type == pygame.KEYDOWN:
                if event.key == pygame.K_UP:
                    selected_button_index = max(0, selected_button_index - 1)
                    using_keyboard = True
                elif event.key == pygame.K_DOWN:
                    selected_button_index = min(len(buttons) - 1, selected_button_index + 1)
                    using_keyboard = True

        # Auto-scroll logic
        if using_keyboard:
            # Check if the selected button is off the bottom of the screen
            if selected_button_index >= visible_buttons_count:
                # Calculate the scroll amount needed to bring the selected button into view
                scroll_to_index = selected_button_index - visible_buttons_count + 1
                target_scroll_offset = scroll_to_index * (button_height + button_spacing)
                adjust_scrollbar(scrollbar, target_scroll_offset, total_saves_height, scrollbar.height)

        # Update button highlighting and interaction
        scroll_offset = scrollbar.get_scroll_percentage() * (total_saves_height - scrollbar.height)
        for idx, button in enumerate(buttons):
            button.rect.y = 100 + idx * (button_height + button_spacing) - scroll_offset
            button.highlighted = (idx == selected_button_index)
            button.update(pygame.mouse.get_pos(), mouse_up, keyboard_navigation=using_keyboard)
            button.draw(screen)

        # Update and draw BACK button
        back_btn.update(pygame.mouse.get_pos(), mouse_up)
        back_btn.draw(screen)

        # Update scrollbar
        mouse_pos = pygame.mouse.get_pos()
        scrollbar.is_hovered = scrollbar_dragging or scrollbar.is_over_handle(mouse_pos)
        scrollbar.draw(screen, mouse_pos)

        # Update display
        pygame.display.flip()

    pygame.quit()

"""def display_options_in_pygame(options, title="Choose an option"):
    pygame.init()
    screen = pygame.display.set_mode((1280, 920))
    pygame.display.set_caption(title)
    font = pygame.font.SysFont('pixeled', 32)
    clock = pygame.time.Clock()

    # Create buttons for each option
    buttons = []
    for i, option in enumerate(options):
        rect = pygame.Rect(100, 50 + i * 40, 600, 32)
        buttons.append({"rect": rect, "option": option})

    selected_option = None
    done = False
    while not done:
        screen.fill((255, 255, 255))
        
        for button in buttons:
            pygame.draw.rect(screen, (0, 192, 255), button["rect"])
            text = font.render(button["option"], True, (0, 0, 0))
            screen.blit(text, (button["rect"].x + 10, button["rect"].y + 5))

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                done = True
                break
            elif event.type == pygame.MOUSEBUTTONDOWN:
                for i, button in enumerate(buttons):
                    if button["rect"].collidepoint(event.pos):
                        selected_option = i
                        done = True
                        break

        pygame.display.flip()
        clock.tick(30)

    pygame.quit()
    return selected_option
"""

def choose_trainer_to_battle_pygame(screen, game_state, human_trainer, trainers, moves_dict):
    # Load background and other resources
    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()

    # Initialize the frame counters and frame update counters
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
    frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0

    possible_opponents = [trainer for trainer in trainers if trainer != human_trainer]
    trainer_names = [trainer.name for trainer in possible_opponents]

    screen_width, screen_height = screen.get_size()
    button_width, button_height = 400, 100  # Button dimensions
    button_x = (screen_width - button_width) // 2  # Center the button horizontally

    # Create buttons for each trainer
    trainer_buttons = []
    for i, trainer_name in enumerate(trainer_names):
        button_y = 150 + i * 105  # Adjust the vertical spacing here
        trainer_buttons.append(Button(button_x, button_y, button_width, button_height, trainer_name.upper(), function=start_battle_with_trainer, params=[screen, human_trainer, possible_opponents[i], moves_dict, game_state]))

    # Add a back button at the end
    back_button_y = 150 + len(trainer_names) * 105 + 100
    trainer_buttons.append(Button(button_x, back_button_y, button_width, button_height, "BACK", function=pre_battle_menu_pygame, params=[screen, game_state, human_trainer]))

    selected_button_index = 0
    using_keyboard = False

    # Main loop for trainer selection
    running = True
    while running:
        mouse_up = False
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            elif event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True
                using_keyboard = False
            elif event.type == pygame.KEYDOWN:
                using_keyboard = True
                if event.key == pygame.K_DOWN:
                    selected_button_index = (selected_button_index + 1) % len(trainer_buttons)
                elif event.key == pygame.K_UP:
                    selected_button_index = (selected_button_index - 1) % len(trainer_buttons)
                elif event.key == pygame.K_RETURN:
                    trainer_buttons[selected_button_index].clicked = True
                    if trainer_buttons[selected_button_index].function:
                        if trainer_buttons[selected_button_index].params:
                            trainer_buttons[selected_button_index].function(*trainer_buttons[selected_button_index].params)
                        else:
                            trainer_buttons[selected_button_index].function()

        # Update GIF frames
        frame_counter_original += 1
        frame_counter_middle += 1
        frame_counter_top += 1

        if frame_counter_original % 2 == 0:
            current_frame_original = (current_frame_original + 1) % len(gif_images)
        if frame_counter_middle % 2 == 0:
            current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        if frame_counter_top % 2 == 0:
            current_frame_top = (current_frame_top + 1) % len(gif_images_top)

        # Draw background and GIFs
        screen.blit(bg_image, (0, 0))
        screen.blit(gif_images[current_frame_original], (800, 600))
        screen.blit(gif_images_middle[current_frame_middle], (0, 0))
        screen.blit(gif_images_top[current_frame_top], (0, 0))

        # Update and draw buttons
        for i, button in enumerate(trainer_buttons):
            if using_keyboard and i == selected_button_index:
                button.highlighted = True
            else:
                button.highlighted = False
            button.update(pygame.mouse.get_pos(), mouse_up, keyboard_navigation=using_keyboard)
            button.draw(screen)

        pygame.display.flip()
        pygame.time.Clock().tick(60)

def save_game_pygame(screen, game_state, human_trainer):
    # Load resources (background and GIFs)
    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()
    
    # Initialize the frame counters
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3

    font = pygame.font.Font(None, 32)
    
    # Determine the size of the screen
    screen_width, screen_height = screen.get_size()
    
    # Define the size of the input box and button
    input_box_width, input_box_height = 400, 100
    button_width, button_height = 400, 100
    
    # Calculate the positions to center the input box and button
    input_box_x = (screen_width - input_box_width) // 2
    input_box_y = (screen_height - (2 * input_box_height + button_height)) // 2
    
    # Create input boxes
    save_name_input_box = InputBox(input_box_x, input_box_y, input_box_width, input_box_height, font, text="Save Name")
    additional_data_input_box = InputBox(input_box_x, input_box_y + input_box_height + 10, input_box_width, input_box_height, font, text="Additional Data")
    
    input_boxes = [save_name_input_box, additional_data_input_box]
    active_input_box = 0  # index of the currently active input box
    confirmation_label = None

    # Add a flag to indicate when the saving process is complete
    save_completed = False

    def save_game_action(save_name_input_box, additional_data_input_box, human_trainer, trainers, pokemons, items, screen, game_state):
        nonlocal confirmation_label
        save_name = save_name_input_box.get_text()
        additional_data = additional_data_input_box.get_text()
        
        with open(f'{save_name}.pkl', 'wb') as f:
            pickle.dump((human_trainer, trainers, pokemons, items, additional_data), f)
        
        confirmation_label = font.render("Your game has been saved successfully", True, (0, 0, 0))
        pygame.time.wait(2000)  # Wait for 2 seconds to let user read the confirmation
        
        # Set the flag to indicate saving is complete
        save_completed = True

        # Return to pre-battle menu
        pre_battle_menu_pygame(screen, game_state, game_state['human_trainer'])

        

    # Modify the button creation to include additional parameters
    enter_button = Button(input_box_x, input_box_y + 2 * (input_box_height + 10), button_width, button_height, text="Enter", function=save_game_action, params=[save_name_input_box, additional_data_input_box, human_trainer, game_state['trainers'], game_state['pokemons'], game_state['items'], screen, game_state])


    running = True
    while running:
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            
            if event.type == pygame.MOUSEBUTTONDOWN:
                for i, box in enumerate(input_boxes):
                    if box.rect.collidepoint(event.pos):
                        box.active = True
                        active_input_box = i
                    else:
                        box.active = False
                        
            
            if event.type == pygame.KEYDOWN:
                if event.key == pygame.K_TAB:  # To switch between input boxes
                    active_input_box = (active_input_box + 1) % 2
                    input_boxes[active_input_box].active = True
                    input_boxes[(active_input_box - 1) % 2].active = False
                else:
                    input_boxes[active_input_box].handle_event(event)

            enter_button.update(pygame.mouse.get_pos(), event.type == pygame.MOUSEBUTTONUP)

        screen.fill((255, 255, 255))  # Fill the screen with white color
        
        
        # Update frame counters
        current_frame_original = (current_frame_original + 1) % len(gif_images)
        current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        current_frame_top = (current_frame_top + 1) % len(gif_images_top)

        # Render the screen with the background and GIFs
        screen.blit(bg_image, (0, 0))
        screen.blit(gif_images[current_frame_original], (800, 600))  # Adjust this to your preference
        screen.blit(gif_images_middle[current_frame_middle], (0, 0))  # Adjust this to your preference
        screen.blit(gif_images_top[current_frame_top], (0, 0))  # Adjust this to your preference


        for box in input_boxes:
            box.draw(screen)
        
        enter_button.draw(screen)

        # Render confirmation message if available
        if confirmation_label:
            screen.blit(confirmation_label, (screen.get_width() / 2 - confirmation_label.get_width() / 2, 350))
            running = False  # Exit the loop after displaying confirmation

            # Break out of the loop if saving is complete
            if save_completed:
                break

        pygame.display.flip()
        pygame.time.Clock().tick(60)

def delete_saved_game_pygame(screen, game_state):
    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()
    window_width, window_height = screen.get_size()

    # Define positions for the GIFs
    # Bottom GIF
    gif_position_x = 800
    gif_position_y = 600

    # Middle GIF
    gif_middle_position_x = 0
    gif_middle_position_y = 0

    # Top GIF
    gif_top_position_x = 0
    gif_top_position_y = 0

    saves = get_save_files()  # Get list of saved games
    if not saves:
        print("No saved games found.")
        return
    
    def delete_game_action(save_file):
        nonlocal buttons
        os.remove(save_file)
        buttons = [btn for btn in buttons if btn.text != save_file]

    # Define button dimensions and spacing
    button_height = 100
    button_spacing = 10  # Space between buttons

    # Create buttons for each saved game
    buttons = []
    y_pos = 100
    y_increment = button_height + button_spacing  # Combined height and spacing for each button
    for idx, save in enumerate(saves):
        btn_y = y_pos + y_increment * idx  # Calculate the y position for each button
        btn = Button(300, btn_y, 700, button_height, save, function=delete_game_action, params=[save])
        buttons.append(btn)

    # Calculate the total height needed for all buttons
    total_saves_height = len(saves) * y_increment

    # Initialize scrollbar
    scrollbar = Scrollbar(window_width - 130, 100, 40, 700, 100, total_saves_height)




    #back_btn = Button(300, y_pos + y_increment * (len(saves) + 1), 700, 100, "Back", function=None)
    #buttons.append(back_btn)

    # Initialize the frame counters and frame update counters
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
    frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0
    
    # Create the back button
    back_button_width = 200
    back_button_height = 100
    back_button_x = 20
    back_button_y = window_height - back_button_height - 20
    back_btn = Button(back_button_x, back_button_y, back_button_width, back_button_height, "BACK", function=pre_battle_menu_pygame, params=[screen, game_state, game_state['human_trainer']])

    # Changes start here

    # Initialize variables
    selected_button_index = 0  # Initialize with the first button selected
    using_keyboard = False
    visible_buttons_count = 4  # Number of buttons visible at a time
    scrollbar_dragging = False

    def adjust_scrollbar(scrollbar, target_offset, total_height, window_height):
        # Adjust the scrollbar's handle position based on the target offset
        max_scroll = total_height - window_height
        percentage = min(max(target_offset / max_scroll, 0), 1)
        scrollbar.handle_y = scrollbar.y + percentage * (scrollbar.height - scrollbar.handle_height)

    running = True
    while running:
        mouse_up = False
        mouse_moved = False  # Flag to track mouse movement

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            elif event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True
                scrollbar_dragging = False
                if back_btn.rect.collidepoint(pygame.mouse.get_pos()):
                    back_btn.update(pygame.mouse.get_pos(), True)
                    if back_btn.function:
                        back_btn.function(*back_btn.params if back_btn.params else [])
                else:
                    for idx, button in enumerate(buttons):
                        if button.rect.collidepoint(pygame.mouse.get_pos()):
                            button.clicked = True
                            if button.function:
                                button.function(*button.params if button.params else [])
                            selected_button_index = idx
                            using_keyboard = False

            elif event.type == pygame.MOUSEBUTTONDOWN:
                if scrollbar.is_over_handle(event.pos):
                    scrollbar_dragging = True
                    mouse_y_offset = event.pos[1] - scrollbar.handle_y

            elif event.type == pygame.MOUSEMOTION:
                mouse_moved = True
                if scrollbar_dragging:
                    new_handle_y = event.pos[1] - mouse_y_offset
                    scrollbar.move_handle(new_handle_y - scrollbar.handle_y)
                else:
                    for idx, button in enumerate(buttons):
                        if button.rect.collidepoint(event.pos):
                            selected_button_index = idx
                            using_keyboard = False

            elif event.type == pygame.KEYDOWN:
                if event.key == pygame.K_UP:
                    selected_button_index = max(0, selected_button_index - 1)
                    using_keyboard = True
                elif event.key == pygame.K_DOWN:
                    selected_button_index = min(len(buttons) - 1, selected_button_index + 1)
                    using_keyboard = True

        # Update button highlighting and handle auto-scroll logic
        if using_keyboard:
            for idx, button in enumerate(buttons):
                button.highlighted = (idx == selected_button_index)

            # Auto-scroll logic
            if selected_button_index >= visible_buttons_count:
                # Calculate the scroll amount needed to bring the selected button into view
                scroll_to_index = selected_button_index - visible_buttons_count + 1
                target_scroll_offset = scroll_to_index * (button_height + button_spacing)
                adjust_scrollbar(scrollbar, target_scroll_offset, total_saves_height, scrollbar.height)
            elif selected_button_index < visible_buttons_count:
                adjust_scrollbar(scrollbar, 0, total_saves_height, scrollbar.height)

        # Update button interaction and drawing
        scroll_offset = scrollbar.get_scroll_percentage() * (total_saves_height - scrollbar.height)
        for idx, button in enumerate(buttons):
            button.rect.y = y_pos + idx * y_increment - scroll_offset
            button.update(pygame.mouse.get_pos(), mouse_up, keyboard_navigation=using_keyboard)
            button.draw(screen)






        # Update GIF frames every 10 refreshes
        frame_counter_original += 1
        frame_counter_middle += 1
        frame_counter_top += 1
        
        if frame_counter_original % 2 == 0:
            current_frame_original = (current_frame_original + 1) % len(gif_images)
        if frame_counter_middle % 2 == 0:
            current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        if frame_counter_top % 2 == 0:
            current_frame_top = (current_frame_top + 1) % len(gif_images_top)

        screen.blit(bg_image, (0, 0))  # Draw the background image

        # Draw the current frames of the GIFs
        screen.blit(gif_images[current_frame_original], (gif_position_x, gif_position_y))
        screen.blit(gif_images_middle[current_frame_middle], (gif_middle_position_x, gif_middle_position_y))
        screen.blit(gif_images_top[current_frame_top], (gif_top_position_x, gif_top_position_y))
        # Update and draw scrollbar
        mouse_pos = pygame.mouse.get_pos()
        scrollbar.is_hovered = scrollbar_dragging or scrollbar.is_over_handle(mouse_pos)
        scrollbar.draw(screen, mouse_pos)

        # Draw each button
        for button in buttons:
            button.draw(screen)

        # Update the back button
        back_btn.update(mouse_pos, mouse_up)  # Add this line to update the back button
        back_btn.draw(screen)

        pygame.display.flip()  # Update the display
        pygame.time.Clock().tick(60)  # Limit the frame rate to 60 FPS

def visit_pokecenter_pygame(trainer, pre_battle_menu_function, screen, game_state, trainers, pokemons):
    # Removed pygame.init()
    screen = pygame.display.set_mode((1280, 920), pygame.DOUBLEBUF)
    pygame.display.set_caption("Pokecenter")

    font = pygame.font.SysFont('pixeled', 24)
    white = (255, 255, 255)
    black = (0, 0, 0)

    # If you have a background image of a Pokecenter, you can load and display it
    # bg_image = pygame.image.load("pokecenter_bg.jpg")

    running = True
    stage = 1  # Use stages to control the display message

    while running:
        screen.fill(white)
        # If you have a background image, you can blit (draw) it on the screen
        # screen.blit(bg_image, (0, 0))

        if stage == 1:
            message = f"{trainer.name} visited the Pokecenter."
        else:
            message = "All your Pokémon have been healed to full health."

        text = font.render(message, True, black)
        text_rect = text.get_rect(center=(400, 300))  # Center the text on the screen
        screen.blit(text, text_rect)

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            elif event.type == pygame.KEYDOWN:
                if event.key == pygame.K_RETURN:  # Proceed to the next stage/message with Enter key
                    if stage == 1:
                        for pokemon in trainer.pokemon_list:
                            pokemon.current_health = pokemon.max_health
                            for move in pokemon.moves:
                                move.pp = move.max_pp
                        stage += 1

                        # Update the game_state with the healed Pokémon
                        game_state['human_trainer'] = trainer
                        game_state['pokemons'] = pokemons  # Update the Pokémon data

                    else:
                        running = False  # Exit after showing the second message

        pygame.display.flip()
        pygame.time.Clock().tick(30)

    # After exiting the Pokecenter, transition back to the pre-battle menu
    # Pass the missing arguments: trainers, pokemons, and game_state
    pre_battle_menu_pygame(screen, game_state, trainer)

def battle_random_trainer_pygame(human_trainer, trainers, moves_dict, screen, game_state):
    
    possible_opponents = [trainer for trainer in trainers if trainer != human_trainer]
    white = (255, 255, 255)
    black = (0, 0, 0)
    font = pygame.font.Font(font_path, 24)
    
    if possible_opponents:
        opponent = deepcopy(random.choice(possible_opponents))
        message = f"You will battle {opponent.name}!"
        
        # Create a PygameBattle instance and start the battle
        battle = PygameBattle(game_state, human_trainer, opponent, moves_dict, human_trainer)
        battle.start()  # This will start the battle and block until the battle is over

    else:
        message = "No other trainers available to battle."
        screen.fill(white)
        text = font.render(message, True, black)
        text_rect = text.get_rect(center=(400, 300))
        screen.blit(text, text_rect)
        pygame.display.flip()
        pygame.time.Clock().tick(30)

def battle_wild_pokemon_menu_pygame(human_trainer, pokemons, game_state, screen, font):
    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()
    
    # Initialize the frame counters and frame update counters
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3

    regions = list(set([region for pokemon in pokemons.values() for region in pokemon.region if region and str(region).lower() != 'nan']))
    chosen_region = choose_region_pygame(regions, screen, font)
    if chosen_region is None:
        return
    sub_regions = list(set([sub_region for pokemon in pokemons.values() for sub_region in pokemon.sub_region if chosen_region in pokemon.region and sub_region and str(sub_region).lower() != 'nan']))
    chosen_sub_region = choose_sub_region_pygame(sub_regions, screen, font)
    if chosen_sub_region is None:
        return
    if chosen_sub_region == "":
        chosen_sub_region = None
    
    running = True
    while running:
        # Update GIF frames
        current_frame_original = (current_frame_original + 1) % len(gif_images)
        current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        current_frame_top = (current_frame_top + 1) % len(gif_images_top)

        # Render the screen with the background and GIFs
        render_screen(screen, bg_image, gif_images, current_frame_original, gif_images_middle, current_frame_middle, gif_images_top, current_frame_top, [], False, False)

        # Start wild battle (this part needs further details on how the battle is handled)
        message = font.render("Starting wild battle", True, (0, 0, 0))
        screen.blit(message, (400, 300))
        pygame.display.flip()
        
        try:
            # This is just a placeholder. Your actual battle logic goes here.
            human_trainer.battle_wild_pokemon(chosen_region, chosen_sub_region, pokemons, game_state)
            
            continue_battle = continue_battle_prompt_pygame(screen, font)
            if continue_battle == 0:
                running = False
        except ExitBattle:
            message = font.render("Battle ended prematurely", True, (0, 0, 0))
            screen.blit(message, (400, 320))
            pygame.display.flip()
        # Handle events like keypresses or mouse clicks
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
                pygame.quit()
                return

def choose_region_pygame(regions, screen, font):
    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()
    
    # Initialize the frame counters
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3

    # Calculate the horizontal center for the buttons
    screen_width = screen.get_width()
    button_width = 400
    center_x = (screen_width - button_width) // 2

    # Create buttons for region selection, centered on the screen
    region_buttons = []
    for i, region in enumerate(regions, 1):
        button_y = 20 + i * 110
        region_buttons.append(Button(center_x, button_y, button_width, 100, region.upper()))

    selected_button_index = 0
    using_keyboard = False

    running = True
    while running:
        mouse_up = False
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                return None
            if event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True

            if event.type == pygame.KEYDOWN:
                using_keyboard = True
                if event.key == pygame.K_DOWN:
                    selected_button_index = (selected_button_index + 1) % len(region_buttons)
                elif event.key == pygame.K_UP:
                    selected_button_index = (selected_button_index - 1) % len(region_buttons)
                elif event.key == pygame.K_RETURN:
                    return regions[selected_button_index]

        # Update GIF frames
        current_frame_original = (current_frame_original + 1) % len(gif_images)
        current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        current_frame_top = (current_frame_top + 1) % len(gif_images_top)

        # Highlight the currently selected button
        for i, button in enumerate(region_buttons):
            if i == selected_button_index:
                button.highlighted = True
            else:
                button.highlighted = False

        # Render the screen with the background and GIFs
        render_screen(screen, bg_image, gif_images, current_frame_original, gif_images_middle, current_frame_middle, gif_images_top, current_frame_top, region_buttons, using_keyboard, mouse_up)

        # Check if any button has been clicked
        for button in region_buttons:
            if button.clicked:
                return regions[region_buttons.index(button)]
            
        pygame.display.flip()
        pygame.time.Clock().tick(60)

def choose_sub_region_pygame(sub_regions, screen, font):
    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()

    # Initialize the frame counters
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3

    # Calculate the horizontal center for the buttons
    screen_width = screen.get_width()
    button_width = 400
    center_x = (screen_width - button_width) // 2

    # Create buttons for sub-region selection, centered on the screen
    sub_region_buttons = [Button(center_x, 50, button_width, 100, "ENTIRE REGION")]

    for i, sub_region in enumerate(sub_regions, 1):
        button_y = 60 + i * 110
        sub_region_buttons.append(Button(center_x, button_y, button_width, 100, sub_region.upper()))

    selected_button_index = 0
    using_keyboard = False

    running = True
    while running:
        mouse_up = False
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                return None
            if event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True
            if event.type == pygame.KEYDOWN:
                using_keyboard = True
                if event.key == pygame.K_DOWN:
                    selected_button_index = (selected_button_index + 1) % len(sub_region_buttons)
                elif event.key == pygame.K_UP:
                    selected_button_index = (selected_button_index - 1) % len(sub_region_buttons)
                elif event.key == pygame.K_RETURN:
                    if selected_button_index == 0:
                        return ""
                    return sub_regions[selected_button_index - 1]

        # Update GIF frames
        current_frame_original = (current_frame_original + 1) % len(gif_images)
        current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        current_frame_top = (current_frame_top + 1) % len(gif_images_top)

        # Highlight the currently selected button
        for i, button in enumerate(sub_region_buttons):
            if i == selected_button_index:
                button.highlighted = True
            else:
                button.highlighted = False

        # Render the screen with the background and GIFs
        render_screen(screen, bg_image, gif_images, current_frame_original, gif_images_middle, current_frame_middle, gif_images_top, current_frame_top, sub_region_buttons, using_keyboard, mouse_up)

        # Check if any button has been clicked
        for button in sub_region_buttons:
            if button.clicked:
                if sub_region_buttons.index(button) == 0:
                    return ""
                return sub_regions[sub_region_buttons.index(button) - 1]
            

        pygame.display.flip()
        pygame.time.Clock().tick(60)

def continue_battle_prompt_pygame(screen, font):
    running = True
    while running:
        screen.fill((255, 255, 255))
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                pygame.quit()
                return 0
            elif event.type == pygame.MOUSEBUTTONDOWN:
                x, y = pygame.mouse.get_pos()
                if 100 <= x <= 400:
                    if 100 <= y <= 130:  # Clicked on "Yes"
                        return 1
                    elif 150 <= y <= 180:  # Clicked on "No"
                        return 0

        screen.blit(font.render("Would you like to continue battling wild Pokemon?", True, (0, 0, 0)), (50, 50))
        pygame.draw.rect(screen, (0, 255, 0), (100, 100, 300, 30))  # Green rectangle for "Yes"
        pygame.draw.rect(screen, (255, 0, 0), (100, 150, 300, 30))  # Red rectangle for "No"
        screen.blit(font.render("Yes", True, (0, 0, 0)), (250, 105))
        screen.blit(font.render("No", True, (0, 0, 0)), (250, 155))
        pygame.display.flip()

def visit_pokemart_pygame(screen, trainer, items, font, game_state):
    # Load resources - this includes background and GIF frames
    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()

    # Initialize the frame counters for the GIF animations
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
    frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0

    item_buttons = []
    trainer_item_buttons = []  # Buttons for trainer's items
    y_pos = 100
    y_pos_buttons = 20
    y_increment = 110
    items_per_page = 5  # Number of items to display per page
    current_page = 0  # Current page

    def refresh_item_buttons():
        # This function is defined within the scope of visit_pokemart_pygame
        # and can access current_page as a non-local variable.
        nonlocal current_page
        load_items(current_page)

    
    def buy_item_pygame(trainer, item):
        if trainer.coins >= item.price:
            trainer.coins -= item.price  # Deduct the price from trainer's coins
            bought_item = copy.deepcopy(item)  # Create a new instance of the item
            trainer.add_item(bought_item)  # Add the new item to trainer's inventory
            print(f"You bought {bought_item.name} for {bought_item.price} coins.")
            refresh_item_buttons()  # Refresh the buttons to reflect the changes
        else:
            print("You don't have enough coins to buy this item.")

    def sell_item_pygame(trainer, item):
        item_found = False
        for i, (trainer_item, quantity) in enumerate(trainer.items):
            if trainer_item.name == item.name:
                item_found = True
                sell_price = int(0.75 * trainer_item.price)  # Calculate the sell price as 75% of the item's price
                trainer.coins += sell_price  # Add the sell price to trainer's coins
                if quantity > 1:
                    trainer.items[i] = (trainer_item, quantity - 1)  # Decrease quantity if more than 1
                else:
                    trainer.items.pop(i)  # Remove the item if quantity is 1
                print(f"You sold {item.name} for {sell_price} coins.")
                refresh_item_buttons()  # Refresh the buttons to reflect the changes
                break

        if not item_found:
            print("You don't have this item to sell.")

    def next_page():
        nonlocal current_page
        if (current_page + 1) * items_per_page < len(items):
            current_page += 1
            load_items(current_page)

    def prev_page():
        nonlocal current_page
        if current_page > 0:
            current_page -= 1
            load_items(current_page)

    def load_items(page):
        nonlocal item_buttons, trainer_item_buttons
        item_buttons = []
        trainer_item_buttons = []

        for i, item_name in enumerate(items, 1):
            if page * items_per_page <= i <= (page + 1) * items_per_page - 1:
                item = items[item_name]  # Get the item object from the dictionary
                btn = Button(25, y_pos + ((i - page * items_per_page) * y_increment), 600, 100,
                             f"{item.name.upper()} : {item.price}", function=buy_item_pygame,
                             params=[trainer, item])
                item_buttons.append(btn)

        for i, (item, quantity) in enumerate(trainer.items, 1):
            btn = Button(640, y_pos + (i * y_increment), 600, 100,
                         f"{item.name.upper()} ({quantity}) : {int(item.price * 0.75)}", function=sell_item_pygame,
                         params=[trainer, item])
            trainer_item_buttons.append(btn)

    load_items(current_page)

    next_page_button = Button(275, y_pos_buttons + (items_per_page + 1) * y_increment, 200, 100, "NEXT", function=next_page)
    prev_page_button = Button(50, y_pos_buttons + (items_per_page + 1) * y_increment, 200, 100, "PREV", function=prev_page)


    human_trainer = trainer
    exit_button = Button(540, y_pos_buttons + (items_per_page + 2) * y_increment, 200, 100, "EXIT", function=exit_pokemart, params=[screen, human_trainer, items, game_state])
    
    running = True
    while running:
        mouse_up = False
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            if event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True

        screen.fill((255, 255, 255))
         # Update GIF frames every 10 refreshes (you can adjust this rate)
        frame_counter_original += 1
        frame_counter_middle += 1
        frame_counter_top += 1

        if frame_counter_original % 2 == 0:
            current_frame_original = (current_frame_original + 1) % len(gif_images)
        if frame_counter_middle % 2 == 0:
            current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        if frame_counter_top % 2 == 0:
            current_frame_top = (current_frame_top + 1) % len(gif_images_top)

        # Draw the background image
        screen.blit(bg_image, (0, 0))

        # Draw the GIFs
        screen.blit(gif_images[current_frame_original], (800, 600))  # Adjust position as needed
        screen.blit(gif_images_middle[current_frame_middle], (0, 0))  # Centered middle gif
        screen.blit(gif_images_top[current_frame_top], (0, 0))  # Top gif flipped

        for btn in item_buttons:
            btn.update(pygame.mouse.get_pos(), mouse_up)
            btn.draw(screen)

        for btn in trainer_item_buttons:
            btn.update(pygame.mouse.get_pos(), mouse_up)
            btn.draw(screen)

        exit_button.update(pygame.mouse.get_pos(), mouse_up)
        exit_button.draw(screen)

        coins_display = font.render(f"COINS: {trainer.coins}", True, (255, 255, 255))
        screen.blit(coins_display, (100, 0))

        next_page_button.update(pygame.mouse.get_pos(), mouse_up)
        prev_page_button.update(pygame.mouse.get_pos(), mouse_up)

        next_page_button.draw(screen)
        prev_page_button.draw(screen)

        pygame.display.flip()
        pygame.time.Clock().tick(60)

def exit_pokemart(screen, trainer, items, game_state):
    
    human_trainer = trainer
    items = game_state['items']
    trainers = game_state['trainers']
    pokemons = game_state['pokemons']
    # Implement logic to exit the pokemart and return to the manage menu.
    manage_menu_pygame(screen, human_trainer, items, trainers, pokemons, game_state)  # You need to define this function to manage the menu.

def update_item_quantity_pygame(trainer, item):
    print(f"Inside update_item_quantity, item: {item}")
    if item is None:
        print("Error: item is None")
        return

    if not isinstance(trainer, Trainer):
        print("Error: Invalid trainer object")
        return

    if not isinstance(trainer.items, list):
        print("Error: Invalid items list in the trainer")
        return

    index_to_remove = None
    for i, item_info in enumerate(trainer.items):
        if item_info[0].name == item[0].name:  # Access the Item object at index 0
            print(f"Decrementing item quantity in list: {item[0].name}")
            item_info[1] -= 1
            if item_info[1] <= 0:
                index_to_remove = i
            break

    # If the item's quantity reaches 0, remove it from the list
    if index_to_remove is not None:
        trainer.items.pop(index_to_remove)

def get_pokemon_image_path(pokemon_name, pokemons):
    """Return the path to the image for the given Pokémon."""
    pokemon_details = pokemons.get(pokemon_name)
    if not pokemon_details:
        raise ValueError(f"No Pokemon found with the name {pokemon_name}")
    pokemon_index = pokemon_details.index
    formatted_index = f"{pokemon_index:04}"
    #return os.path.join("F:\\Scripts\\PokePyMain-main\\pokemon_pics", f"{formatted_index}{pokemon_name}.png")
    #return os.path.join("C:\\Users\matth\\OneDrive\\PokePy\\PokePyMain-main\\pokemon_pics", f"{formatted_index}{pokemon_name}.png")
    #return os.path.join("C:\\Users\Tusa\\OneDrive\\PokePy\\PokePyMain-main\\pokemon_pics", f"{formatted_index}{pokemon_name}.png")
    
    return os.path.join("pokemon_pics", f"{formatted_index}{pokemon_name}.png")

def access_storage_pygame(screen, human_trainer, trainers, pokemons, items, game_state):
    running = True

    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()
    
    # Initialize the frame counters for the GIF animations
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
    frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0
    

    y_pos = 100

    def get_pokemon_image_path(pokemon_name):
        """Return the path to the image for the given Pokémon."""
        pokemon_details = pokemons.get(pokemon_name)
        if not pokemon_details:
            raise ValueError(f"No Pokemon found with the name {pokemon_name}")
        pokemon_index = pokemon_details.index
        formatted_index = f"{pokemon_index:04}"
        #return os.path.join("F:\\Scripts\\PokePyMain-main\\pokemon_pics", f"{formatted_index}{pokemon_name}.png")
        #return os.path.join("C:\\Users\matth\\OneDrive\\PokePy\\PokePyMain-main\\pokemon_pics", f"{formatted_index}{pokemon_name}.png")
        #return os.path.join("C:\\Users\Tusa\\OneDrive\\PokePy\\PokePyMain-main\\pokemon_pics", f"{formatted_index}{pokemon_name}.png")
    
        return os.path.join("pokemon_pics", f"{formatted_index}{pokemon_name}.png")
    


    # Create a BACK button
    back_btn = Button(580, 775, 200, 100, "BACK", function=manage_menu_pygame, params=[screen, human_trainer, items, trainers, pokemons, game_state])



    while running:
        # Handle user input first
        mouse_up = False
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            if event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True
        
        # Draw the background and GIF animations first
        screen.fill((255, 255, 255))  # Fill the screen with white color
        screen.blit(bg_image, (0, 0))
        screen.blit(gif_images[current_frame_original], (800, 600))  # Adjust positions as needed
        screen.blit(gif_images_middle[current_frame_middle], (0, 0))  # Centered middle gif
        screen.blit(gif_images_top[current_frame_top], (0, 0))  # Top gif flipped

        # Update GIF frames every few refreshes (adjust as needed)
        frame_counter_original += 1
        frame_counter_middle += 1
        frame_counter_top += 1

        if frame_counter_original % 2 == 0:
            current_frame_original = (current_frame_original + 1) % len(gif_images)
        if frame_counter_middle % 2 == 0:
            current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        if frame_counter_top % 2 == 0:
            current_frame_top = (current_frame_top + 1) % len(gif_images_top)

        # Reset y_pos for drawing Pokémon images and buttons
        y_pos = 100
        y_increment = 110
        # Create buttons for current team and storage Pokémon
        current_team_buttons = []
        storage_buttons = []
        # Create buttons for current team Pokémon
        x_pos_current_team = 20
        for i, pokemon in enumerate(human_trainer.pokemon_list):
            button_text = f"{i + 1}. {pokemon.name.upper()}"
            current_pokemon_btn = Button(
                x_pos_current_team + 100,   # Adjusted for space for images
                y_pos,
                500,
                100,
                button_text,
                function=transfer_pokemon_to_storage,
                params=[human_trainer, i],
            )
            current_team_buttons.append(current_pokemon_btn)
            pokemon_image = pygame.image.load(get_pokemon_image_path(pokemon.name))
            scaled_pokemon_image = pygame.transform.scale(pokemon_image, (80, 80))
            screen.blit(scaled_pokemon_image, (x_pos_current_team, y_pos))
            y_pos += y_increment

        y_pos = 100  # Reset y_pos for storage Pokémon

        # Create buttons for storage Pokémon
        x_pos_storage = 640
        for i, pokemon in enumerate(human_trainer.storage):
            button_text = f"{i + 1}. {pokemon.name.upper()}"
            storage_pokemon_btn = Button(
                x_pos_storage + 100,   # Adjusted for space for images
                y_pos,
                500,
                100,
                button_text,
                function=transfer_pokemon_to_current_team,
                params=[human_trainer, i],
            )
            storage_buttons.append(storage_pokemon_btn)
            pokemon_image = pygame.image.load(get_pokemon_image_path(pokemon.name))
            scaled_pokemon_image = pygame.transform.scale(pokemon_image, (80, 80))
            screen.blit(scaled_pokemon_image, (x_pos_storage, y_pos))
            y_pos += y_increment


        # Handle user input
        mouse_up = False
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            if event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True


        # Update and draw buttons for current team Pokémon
        for button in current_team_buttons:
            button.update(pygame.mouse.get_pos(), mouse_up)
            button.draw(screen)

        # Update and draw buttons for storage Pokémon
        for button in storage_buttons:
            button.update(pygame.mouse.get_pos(), mouse_up)
            button.draw(screen)

        # Update and draw BACK button
        back_btn.update(pygame.mouse.get_pos(), mouse_up)
        back_btn.draw(screen)

        pygame.display.flip()  # Update the display

        pygame.time.Clock().tick(60)  # Limit the frame rate to 60 FPS

# Function to transfer a Pokémon from the current team to storage
def transfer_pokemon_to_storage(human_trainer, index):
    if len(human_trainer.pokemon_list) <= 1:
        print("You must have at least one Pokémon in your team.")
        return
    if len(human_trainer.storage) >= 50:
        print("Your storage is full. You can't deposit more Pokémon.")
        return
    pokemon_to_transfer = human_trainer.pokemon_list.pop(index)
    human_trainer.storage.append(pokemon_to_transfer)
# Function to transfer a Pokémon from storage to the current team
def transfer_pokemon_to_current_team(human_trainer, index):
    if len(human_trainer.pokemon_list) >= 6:
        print("Your team is full. You can't withdraw more Pokémon.")
        return
    pokemon_to_transfer = human_trainer.storage.pop(index)
    human_trainer.pokemon_list.append(pokemon_to_transfer)

# Global lists for proposed trade buttons
proposed_trade_human_buttons = []
proposed_trade_other_buttons = []

#Trade pokemon functions
def trade_pokemon_select_trainer_pygame(screen, human_trainer, trainers, game_state):
    running = True
    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()

    # Initialize the frame counters and frame update counters
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
    frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0

    # Filter out the human trainer from the list of trainers to trade with
    other_trainers = [trainer for trainer in trainers if trainer != human_trainer]

    y_pos = 100
    y_increment = 110
    trainer_buttons = []

    for i, trainer in enumerate(other_trainers):
        button_text = f"{trainer.name.upper()}"
        trainer_btn = Button(
            440,
            y_pos,
            400,
            100,
            button_text,
            function=trade_pokemon_window_pygame,
            params=[screen, human_trainer, trainer, trainers, game_state]
        )
        trainer_buttons.append(trainer_btn)
        y_pos += y_increment

    back_btn = Button(540, 700, 200, 100, "BACK", function=manage_menu_pygame, params=[screen, human_trainer, game_state['items'], trainers, game_state['pokemons'], game_state])

    # Variable to track the selected button index
    selected_button_index = 0
    using_keyboard = False

    # Combine all buttons into a single list for easier navigation
    all_buttons = trainer_buttons + [back_btn]

    while running:
        mouse_up = False  # Initialize mouse_up to False at the start of the loop
        screen.fill((255, 255, 255))  # Fill screen with white color

        
        # Update GIF frames every few refreshes (adjust as needed)
        frame_counter_original += 1
        frame_counter_middle += 1
        frame_counter_top += 1
        
        if frame_counter_original % 2 == 0:
            current_frame_original = (current_frame_original + 1) % len(gif_images)
        if frame_counter_middle % 2 == 0:
            current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        if frame_counter_top % 2 == 0:
            current_frame_top = (current_frame_top + 1) % len(gif_images_top)

        # Draw the background and GIFs first
        screen.blit(bg_image, (0, 0))
        screen.blit(gif_images[current_frame_original], (800, 600))  # Adjust positions as needed
        screen.blit(gif_images_middle[current_frame_middle], (0, 0))  # Centered middle GIF
        screen.blit(gif_images_top[current_frame_top], (0, 0))  # Top GIF flipped


        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            if event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True

            # Handling keyboard events
            if event.type == pygame.KEYDOWN:
                using_keyboard = True
                if event.key == pygame.K_DOWN:
                    selected_button_index = (selected_button_index + 1) % len(all_buttons)
                elif event.key == pygame.K_UP:
                    selected_button_index = (selected_button_index - 1) % len(all_buttons)
                elif event.key == pygame.K_RETURN:
                    all_buttons[selected_button_index].clicked = True
                    if all_buttons[selected_button_index].function:
                        all_buttons[selected_button_index].function(*all_buttons[selected_button_index].params)

        # Highlight the selected button if using keyboard
        for i, button in enumerate(all_buttons):
            button.update(pygame.mouse.get_pos(), mouse_up, keyboard_navigation=using_keyboard)
            if using_keyboard:
                button.highlighted = (i == selected_button_index)
            button.draw(screen)

        pygame.display.flip()
        pygame.time.Clock().tick(60)

    # Clear the proposed_trade_list when exiting the trading window
    global proposed_trade_list
    proposed_trade_list.clear()

    # Reactivate all Pokémon buttons. However, note that we don't have direct access 
    # to Pokémon buttons here. You might need to store references to these buttons 
    # globally or pass them as arguments to this function to reactivate them.
    # The following is a placeholder and may not work without modifications:
    for button in human_trainer.pokemon_list + other_trainers:
        button.active = True

def create_pokemon_buttons(trainer, x_pos, y_pos, y_increment, human_trainer, human_buttons, other_buttons):
    """Create Pokémon buttons for a given trainer."""
    buttons = []
    for i, pokemon in enumerate(trainer.pokemon_list):
        # In trade_pokemon_window_pygame or any other function where you create PokemonButton instances
        offer_btn = PokemonButton(
            x_pos,
            y_pos,
            300,
            50,
            pokemon,
            game_state,  # Pass game_state here
            function=offer_for_trade,
            params=[trainer, human_trainer, i, human_buttons, other_buttons]
        )
        buttons.append(offer_btn)
        y_pos += y_increment
    return buttons

def trade_pokemon_window_pygame(screen, human_trainer, other_trainer, trainers, game_state):
    global human_buttons_x_pos, other_buttons_x_pos
    global trade_completed  # Ensure that this is a global variable
    running = True
    trade_completed = False  # Initialize the trade_completed variable

    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()

    # Initialize the frame counters and frame update counters
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
    frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0

    screen_width = screen.get_width()
    human_buttons_x_pos = screen_width * 0.25  # 25% of the screen width for human buttons
    other_buttons_x_pos = screen_width * 0.75  # 75% of the screen width for other trainer buttons


    y_pos = 100
    y_increment = 60

    def refresh_pokemon_buttons(human_trainer, other_trainer, screen_width):
        # Clear existing buttons
        human_pokemon_buttons.clear()
        other_trainer_pokemon_buttons.clear()

        y_pos = 100
        y_increment = 60

        # Create new buttons for human trainer's Pokémon
        for i, pokemon in enumerate(human_trainer.pokemon_list):
            button_text = f"{pokemon.name.upper()}"
            offer_btn = Button(
                screen_width * 0.25 - 150,  # 25% of the screen width for human buttons
                y_pos,
                300,
                50,
                button_text,
                function=offer_for_trade,
                params=[human_trainer, human_trainer, i, human_pokemon_buttons, other_trainer_pokemon_buttons]
            )
            human_pokemon_buttons.append(offer_btn)
            y_pos += y_increment

        # Reset position for other trainer's Pokémon
        y_pos = 100

        # Create new buttons for other trainer's Pokémon
        for i, pokemon in enumerate(other_trainer.pokemon_list):
            button_text = f"{pokemon.name.upper()}"
            offer_btn = Button(
                screen_width * 0.75 - 150,  # 75% of the screen width for other trainer buttons
                y_pos,
                300,
                50,
                button_text,
                function=offer_for_trade,
                params=[other_trainer, human_trainer, i, human_pokemon_buttons, other_trainer_pokemon_buttons]
            )
            other_trainer_pokemon_buttons.append(offer_btn)
            y_pos += y_increment


    human_pokemon_buttons = []
    other_trainer_pokemon_buttons = []

    # Initialize the proposed trade buttons lists
    proposed_trade_human_buttons = []
    proposed_trade_other_buttons = []


    # Create Pokémon offer buttons for human trainer's Pokémon
    y_pos = 100
    for i, pokemon in enumerate(human_trainer.pokemon_list):
        offer_btn = PokemonButton(
            human_buttons_x_pos - 150,  # Center the button around the x position
            y_pos,
            500,
            50,
            pokemon,
            game_state,  # Pass game_state here
            function=offer_for_trade,
            params=[human_trainer, other_trainer, i, human_pokemon_buttons, other_trainer_pokemon_buttons]
        )
        human_pokemon_buttons.append(offer_btn)
        y_pos += y_increment

    # Create Pokémon offer buttons for other trainer's Pokémon
    y_pos = 100
    for i, pokemon in enumerate(other_trainer.pokemon_list):
        offer_btn = PokemonButton(
            other_buttons_x_pos - 150,  # Center the button around the x position
            y_pos,
            500,
            50,
            pokemon,
            game_state,  # Pass game_state here
            function=offer_for_trade,
            params=[other_trainer, human_trainer, i, human_pokemon_buttons, other_trainer_pokemon_buttons]
        )
        other_trainer_pokemon_buttons.append(offer_btn)
        y_pos += y_increment

    confirm_trade_btn = Button(130, 800, 600, 100, "CONFIRM TRADE", function=confirm_trade, params=[human_trainer, other_trainer, human_pokemon_buttons, other_trainer_pokemon_buttons, screen, game_state, trainers])


    back_btn = Button(750, 800, 200, 100, "BACK", function=trade_pokemon_select_trainer_pygame, params=[screen, human_trainer, trainers, game_state])


    # Initialize keyboard navigation variables
    using_keyboard = False
    selected_button_index = 0
    selected_button_list = human_pokemon_buttons  # Start with human trainer's buttons
    all_buttons = human_pokemon_buttons + other_trainer_pokemon_buttons + [confirm_trade_btn, back_btn]

    while running:
        mouse_up = False


        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            if event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True
                if using_keyboard:
                    using_keyboard = False

            # Update keyboard navigation logic
            if event.type == pygame.KEYDOWN:
                using_keyboard = True

                if event.key == pygame.K_DOWN:
                    # Modify this section to include the new button lists
                    # Check if the current list is human_pokemon_buttons or other_trainer_pokemon_buttons
                    # and the selected index is at the last element
                    if selected_button_list == human_pokemon_buttons and selected_button_index == len(human_pokemon_buttons) - 1:
                        # Check if there are any buttons in proposed_trade_human_buttons
                        if proposed_trade_human_buttons:
                            selected_button_list = proposed_trade_human_buttons
                            selected_button_index = 0
                        else:
                            # Existing logic to move to confirm/back buttons
                            selected_button_list = [confirm_trade_btn, back_btn]
                            selected_button_index = 0
                    # Repeat similar logic for other_trainer_pokemon_buttons
                    elif selected_button_list == other_trainer_pokemon_buttons and selected_button_index == len(other_trainer_pokemon_buttons) - 1:
                        if proposed_trade_other_buttons:
                            selected_button_list = proposed_trade_other_buttons
                            selected_button_index = 0
                        else:
                            selected_button_list = [confirm_trade_btn, back_btn]
                            selected_button_index = 1
                    else:
                        # Existing logic for incrementing selected_button_index
                        selected_button_index = (selected_button_index + 1) % len(selected_button_list)

                elif event.key == pygame.K_UP:
                    # Up arrow key handling
                    if selected_button_list == [confirm_trade_btn, back_btn] and selected_button_index == 0:
                        # Move up from confirm trade to the bottom of human buttons
                        selected_button_list = human_pokemon_buttons
                        selected_button_index = len(human_pokemon_buttons) - 1
                    elif selected_button_list == [confirm_trade_btn, back_btn] and selected_button_index == 1:
                        # Move up from back button to the bottom of other trainer's buttons
                        selected_button_list = other_trainer_pokemon_buttons
                        selected_button_index = len(other_trainer_pokemon_buttons) - 1
                    else:
                        selected_button_index = (selected_button_index - 1) % len(selected_button_list)

                elif event.key in [pygame.K_LEFT, pygame.K_RIGHT]:
                    # Left/Right arrow key handling
                    if selected_button_list in [human_pokemon_buttons, other_trainer_pokemon_buttons]:
                        # Switch between human and other trainer's Pokémon lists
                        selected_button_list = other_trainer_pokemon_buttons if selected_button_list is human_pokemon_buttons else human_pokemon_buttons
                        selected_button_index = min(selected_button_index, len(selected_button_list) - 1)  # Adjust index if new list is shorter
                    elif selected_button_list == [confirm_trade_btn, back_btn]:
                        # Switch between confirm trade and back buttons
                        selected_button_index = 1 - selected_button_index


                elif event.key == pygame.K_RETURN:
                    clicked_button = selected_button_list[selected_button_index]
                    clicked_button.clicked = True
                    if clicked_button == back_btn:
                        # Handle trade cancellation
                        offered_pokemons.clear()
                        proposed_trade_list.clear()
                        # Reactivate all Pokémon buttons here (if necessary)
                        manage_menu_pygame(screen, human_trainer, game_state['items'], trainers, game_state['pokemons'], game_state)
                        running = False  # Exit the trade window
                    elif clicked_button.function:
                        clicked_button.function(*clicked_button.params)
                elif event.key == pygame.K_BACKSPACE:
                    # Trigger the back button function
                    back_btn.clicked = True
                    back_btn.function(*back_btn.params)

        # Update GIF frames every few refreshes (adjust as needed)
        frame_counter_original += 1
        frame_counter_middle += 1
        frame_counter_top += 1
        
        if frame_counter_original % 2 == 0:
            current_frame_original = (current_frame_original + 1) % len(gif_images)
        if frame_counter_middle % 2 == 0:
            current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        if frame_counter_top % 2 == 0:
            current_frame_top = (current_frame_top + 1) % len(gif_images_top)


        # Draw the background and GIFs first
        screen.blit(bg_image, (0, 0))
        screen.blit(gif_images[current_frame_original], (800, 600))  # Adjust positions as needed
        screen.blit(gif_images_middle[current_frame_middle], (0, 0))  # Centered middle GIF
        screen.blit(gif_images_top[current_frame_top], (0, 0))  # Top GIF flipped


        

        # Display Pokémon images next to the buttons
        display_pokemon_images(screen, human_trainer, human_trainer.pokemon_list, 10, 100, game_state)
        display_pokemon_images(screen, other_trainer, other_trainer.pokemon_list, 360, 100, game_state)

        # Update button drawing with keyboard navigation for both trainers' buttons
        for button_set in [human_pokemon_buttons, other_trainer_pokemon_buttons]:
            for i, button in enumerate(button_set):
                button.update(pygame.mouse.get_pos(), mouse_up, keyboard_navigation=using_keyboard)
                if using_keyboard and button_set == selected_button_list and i == selected_button_index:
                    button.highlighted = True
                button.draw(screen)

        # Displaying the proposed trade list
        y_proposed_trade_human = 500  # Start position for human trainer's Pokémon
        y_proposed_trade_other = 500  # Start position for other trainer's Pokémon

        for trainer, pokemon in proposed_trade_list:
            if trainer == human_trainer:
                x_pos = 75
                y_display = y_proposed_trade_human
                y_proposed_trade_human += y_increment
            else:
                x_pos = 450
                y_display = y_proposed_trade_other
                y_proposed_trade_other += y_increment

            pokemon_image = pygame.image.load(get_pokemon_image_path(pokemon.name, game_state['pokemons']))
            scaled_pokemon_image = pygame.transform.scale(pokemon_image, (80, 80))
            screen.blit(scaled_pokemon_image, (x_pos, y_display))

            remove_btn = Button(x_pos + 90, y_display, 250, 60, pokemon.name.upper(), function=remove_from_trade, params=[trainer, human_trainer, trainer.pokemon_list.index(pokemon), human_pokemon_buttons, other_trainer_pokemon_buttons])
            remove_btn.update(pygame.mouse.get_pos(), mouse_up)
            remove_btn.draw(screen)



        confirm_trade_btn.update(pygame.mouse.get_pos(), mouse_up)
        confirm_trade_btn.draw(screen)

        back_btn.update(pygame.mouse.get_pos(), mouse_up)
        back_btn.draw(screen)

        def draw_highlight(screen, button):
            highlight_color = (255, 255, 0)  # Yellow color for highlight
            highlight_rect = pygame.Rect(button.rect.x, button.rect.y, button.rect.width, button.rect.height)
            pygame.draw.rect(screen, highlight_color, highlight_rect, 2)  # Draw a yellow rectangle around the button

            # Before drawing buttons, reset the highlighted state for all buttons
        for button in all_buttons:
            button.highlighted = False

        # Now, set the highlighted state for the currently selected button
        if using_keyboard:
            selected_button_list[selected_button_index].highlighted = True

        if trade_completed:  # Check if a trade has been completed
            refresh_pokemon_buttons(human_trainer, other_trainer, screen.get_width())
            print(f"trade pokemon window before reset Trade completed: {trade_completed}")
            trade_completed = False  # Reset the flag after refreshing buttons
            print(f"trade pokemon window after reset Trade completed: {trade_completed}")


        # Draw buttons and highlights
        for button in all_buttons:
            button.update(pygame.mouse.get_pos(), mouse_up, keyboard_navigation=using_keyboard)
            button.draw(screen)  # Draw button first
            if using_keyboard and button == selected_button_list[selected_button_index]:
                # Draw highlight over the button here
                draw_highlight(screen, button)  # Implement this function to draw the highlight

        pygame.display.flip()
        pygame.time.Clock().tick(60)

# Global dictionary to store which Pokémon each trainer is offering for trade
offered_pokemons = {}
proposed_trade_list = []

def display_pokemon_images(screen, trainer, pokemon_list, x_pos, y_pos, game_state):
    """Display Pokémon images for a list of Pokémon."""
    y_increment = 60
    for index, pokemon in enumerate(pokemon_list):
        # Skip displaying images for Pokémon being offered for trade
        if (trainer, pokemon) in proposed_trade_list:
            y_pos += y_increment
            continue
        
        pokemon_image = pygame.image.load(get_pokemon_image_path(pokemon.name, game_state['pokemons']))
        scaled_pokemon_image = pygame.transform.scale(pokemon_image, (50, 50))  # Adjust size as necessary
        screen.blit(scaled_pokemon_image, (x_pos, y_pos))
        y_pos += y_increment

def offer_for_trade(trainer, human_trainer, index, human_buttons, other_buttons):
    global offered_pokemons, proposed_trade_list
    global proposed_trade_human_buttons, proposed_trade_other_buttons
    global human_buttons_x_pos, other_buttons_x_pos

    # Ensure index is valid
    if index >= len(trainer.pokemon_list):
        print(f"Invalid index: {index} for trainer's pokemon list")
        return
    # Initialize the trainer in the dictionary if not already present
    if trainer not in offered_pokemons:
        offered_pokemons[trainer] = []

    # Add the Pokémon to the offered list for the trainer

    if index not in offered_pokemons[trainer]:
        offered_pokemons[trainer].append(index)
        proposed_trade_list.append((trainer, trainer.pokemon_list[index]))

        # Define x_pos and y_pos
        if trainer == human_trainer:
            x_pos = human_buttons_x_pos - 150
            y_pos = 500 + len(proposed_trade_human_buttons) * 60  # Example calculation
        else:
            x_pos = other_buttons_x_pos - 150
            y_pos = 500 + len(proposed_trade_other_buttons) * 60  # Example calculation


        # Create a button for the proposed trade
        proposed_button = Button(
            x_pos,  # You need to determine the appropriate x position
            y_pos,  # You need to determine the appropriate y position
            300,
            50,
            trainer.pokemon_list[index].name.upper(),
            function=remove_from_trade,  # Set the appropriate function for removing from trade
            params=[trainer, human_trainer, index, human_buttons, other_buttons]
        )

        # Add the button to the appropriate list
        if trainer == human_trainer:
            proposed_trade_human_buttons.append(proposed_button)
        else:
            proposed_trade_other_buttons.append(proposed_button)
    else:
        # If the Pokémon is already in the list, remove it
        offered_pokemons[trainer].remove(index)
        if (trainer, trainer.pokemon_list[index]) in proposed_trade_list:
            proposed_trade_list.remove((trainer, trainer.pokemon_list[index]))
        # Enable the button
        if trainer == human_trainer:
            human_buttons[index].active = True
        else:
            other_buttons[index].active = True

def remove_from_trade(trainer, human_trainer, index, human_buttons, other_buttons):
    global proposed_trade_list, offered_pokemons
    global proposed_trade_human_buttons, proposed_trade_other_buttons  # Add this line

    # Remove the button from the appropriate list
    for btn_list in [proposed_trade_human_buttons, proposed_trade_other_buttons]:
        for btn in btn_list:
            if btn.params[2] == index and btn.params[0] == trainer:  # Check if this is the correct button
                btn_list.remove(btn)
                break
    
    # Check if the trainer exists in offered_pokemons before deleting
    if trainer in offered_pokemons:
        del offered_pokemons[trainer]

    # Make the original button active and visible again
    if trainer == human_trainer:
        human_buttons[index].active = True
    else:
        other_buttons[index].active = True

def confirm_trade(human_trainer, other_trainer, human_buttons, other_buttons, screen, game_state, trainers):
    global offered_pokemons

    # Check the resulting sizes of the pokemon_list after the trade
    human_offered_len = len(offered_pokemons[human_trainer]) if human_trainer in offered_pokemons else 0
    other_offered_len = len(offered_pokemons[other_trainer]) if other_trainer in offered_pokemons else 0
    
    human_trainer_size_after_trade = len(human_trainer.pokemon_list) + other_offered_len - human_offered_len
    other_trainer_size_after_trade = len(other_trainer.pokemon_list) + human_offered_len - other_offered_len

    if human_trainer_size_after_trade > 6 or other_trainer_size_after_trade > 6:
        print("Trade cannot be completed. One or both trainers will have more than 6 Pokémon after the trade.")
        
        # Resetting logic when trade cannot be completed
        proposed_trade_list.clear()
        offered_pokemons = {}
        
        # Update Pokémon buttons with the current team (effectively resetting them)
        y_pos = 100
        y_increment = 60
        human_buttons.clear()
        human_buttons.extend(create_pokemon_buttons(human_trainer, 75, y_pos, y_increment, human_trainer, human_buttons, other_buttons))
        other_buttons.clear()
        other_buttons.extend(create_pokemon_buttons(other_trainer, 425, y_pos, y_increment, human_trainer, human_buttons, other_buttons))

        # Redraw the updated Pokémon list and images
        screen.fill((255, 255, 255))
        display_pokemon_images(screen, human_trainer, human_trainer.pokemon_list, 10, y_pos, game_state)
        display_pokemon_images(screen, other_trainer, other_trainer.pokemon_list, 360, y_pos, game_state)
        for button in human_buttons + other_buttons:
            button.draw(screen)
        pygame.display.flip()
        
        return

    # Ensure both trainers have offered at least one Pokémon for trade
    if not offered_pokemons.get(human_trainer) or not offered_pokemons.get(other_trainer):
        print("Both trainers must offer at least one Pokémon for trade before confirming.")
        return

    # Transfer Pokémon between trainers
    for index in offered_pokemons[human_trainer]:
        other_trainer.pokemon_list.append(human_trainer.pokemon_list[index])
    for index in offered_pokemons[other_trainer]:
        human_trainer.pokemon_list.append(other_trainer.pokemon_list[index])

    # Remove traded Pokémon from original lists
    for index in sorted(offered_pokemons[human_trainer], reverse=True):
        del human_trainer.pokemon_list[index]
    for index in sorted(offered_pokemons[other_trainer], reverse=True):
        del other_trainer.pokemon_list[index]

    # Reset the offered_pokemons dictionary and proposed_trade_list
    offered_pokemons.clear()
    proposed_trade_list.clear()

    # After completing the trade
    print("Trade completed!")

    # Reset the offered_pokemons dictionary and proposed_trade_list
    offered_pokemons.clear()
    proposed_trade_list.clear()

    # Call manage_menu_pygame to return to the manage menu
    manage_menu_pygame(screen, human_trainer, game_state['items'], trainers, game_state['pokemons'], game_state)


    # After trade logic
    screen_width = screen.get_width()
    human_buttons_x_pos = screen_width * 0.25  # 25% of the screen width for human buttons
    other_buttons_x_pos = screen_width * 0.75  # 75% of the screen width for other trainer buttons

    y_pos = 100
    y_increment = 60

    # Update Pokémon buttons with the current team after the trade
    human_buttons.clear()
    for i, pokemon in enumerate(human_trainer.pokemon_list):
        button_text = f"{pokemon.name.upper()}"
        offer_btn = Button(
            human_buttons_x_pos - 150,  # Center the button around the x position
            y_pos,
            300,
            50,
            button_text,
            function=offer_for_trade,
            params=[human_trainer, human_trainer, i, human_buttons, other_buttons]
        )
        human_buttons.append(offer_btn)
        y_pos += y_increment

    y_pos = 100  # Reset y_pos for other trainer's Pokémon
    other_buttons.clear()
    for i, pokemon in enumerate(other_trainer.pokemon_list):
        button_text = f"{pokemon.name.upper()}"
        offer_btn = Button(
            other_buttons_x_pos - 150,  # Center the button around the x position
            y_pos,
            300,
            50,
            button_text,
            function=offer_for_trade,
            params=[other_trainer, human_trainer, i, human_buttons, other_buttons]
        )
        other_buttons.append(offer_btn)
        y_pos += y_increment

    # Redraw the updated Pokémon list and images
    screen.fill((255, 255, 255))
    display_pokemon_images(screen, human_trainer, human_trainer.pokemon_list, 10, 100, game_state)
    display_pokemon_images(screen, other_trainer, other_trainer.pokemon_list, 360, 100, game_state)
    for button in human_buttons + other_buttons:
        button.draw(screen)
    pygame.display.flip()

"""def battle_trainers_by_team_menu(screen, human_trainer, trainers, moves_dict, game_state):4
    team_names = list(set([trainer.team for trainer in trainers if trainer.name != human_trainer.name]))
    
    # Create buttons for team selection
    team_buttons = []
    for i, team_name in enumerate(team_names, 1):
        button_y = 150 + i * 100  # Increase the vertical spacing here
        team_buttons.append(Button(300, button_y, 200, 50, team_name.upper(), function=sub_team_menu, params=[screen, human_trainer, trainers, moves_dict, team_name, game_state]))

    # Add a back button
    back_button = Button(300, 150 + len(team_names) * 100 + 100, 200, 50, "BACK", function=pre_battle_menu_pygame, params=[screen, game_state, human_trainer])


    # Sub-menu loop
    running = True
    while running:
        mouse_up = False
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            if event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True

        screen.fill((255, 255, 255))  # Fill the screen with white color

        # Update and draw buttons
        for button in team_buttons:
            button.update(pygame.mouse.get_pos(), mouse_up)
            button.draw(screen)
        back_button.update(pygame.mouse.get_pos(), mouse_up)
        back_button.draw(screen)

        pygame.display.flip()  # Update the display

        pygame.time.Clock().tick(60)  # Limit the frame rate to 60 FPS
"""

"""def sub_team_menu(screen, human_trainer, trainers, moves_dict, team_name, game_state):
    trainers_in_team = [trainer for trainer in trainers if trainer.team == team_name and trainer.name != human_trainer.name]

    # Create buttons for trainer selection
    trainer_buttons = []
    for i, trainer in enumerate(trainers_in_team, 1):
        button_y = 150 + i * 80  # Adjust the vertical spacing here
        trainer_buttons.append(Button(300, button_y, 200, 50, trainer.name.upper(), function=start_battle_with_trainer, params=[screen, human_trainer, trainer, moves_dict, game_state]))

    # Add a back button
    back_button = Button(300, 150 + len(trainers_in_team) * 80 + 100, 200, 50, "BACK", function=battle_trainers_by_team_menu, params=[screen, human_trainer, trainers, moves_dict, game_state])

    # Sub-menu loop
    running = True
    while running:
        mouse_up = False
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            if event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True

        screen.fill((255, 255, 255))  # Fill the screen with white color

        # Update and draw buttons
        for button in trainer_buttons:
            button.update(pygame.mouse.get_pos(), mouse_up)
            button.draw(screen)
        back_button.update(pygame.mouse.get_pos(), mouse_up)
        back_button.draw(screen)

        pygame.display.flip()  # Update the display

        pygame.time.Clock().tick(60)  # Limit the frame rate to 60 FPS
"""

def battle_trainers_by_team_menu(screen, human_trainer, trainers, moves_dict, game_state):
    team_names = list(set([trainer.team for trainer in trainers if trainer.name != human_trainer.name]))
    
    # Create buttons for team selection
    window_width, window_height = screen.get_size()
    button_width, button_height = 400, 100
    button_spacing = 20
    total_button_height = (len(team_names) + 1) * button_height + len(team_names) * button_spacing
    start_y = (window_height - total_button_height) / 2

    team_buttons = []
    for i, team_name in enumerate(team_names):
        button_y = start_y + i * (button_height + button_spacing)
        team_buttons.append(Button((window_width - button_width) / 2, button_y, button_width, button_height, team_name.upper(), function=sub_team_menu, params=[screen, human_trainer, trainers, moves_dict, team_name, game_state]))

    # Add a back button
    back_button_y = start_y + len(team_names) * (button_height + button_spacing)
    back_button = Button((window_width - button_width) / 2, back_button_y, button_width, button_height, "BACK", function=pre_battle_menu_pygame, params=[screen, game_state, human_trainer])
    team_buttons.append(back_button)

    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()
    
    # Initialize frame counters and frame update counters
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
    frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0
    selected_button_index = 0
    using_keyboard = False

    running = True
    while running:
        running, using_keyboard, selected_button_index, mouse_up = handle_events(team_buttons, using_keyboard, selected_button_index)
        
        # Update GIF frames every 10 refreshes
        frame_counter_original += 10
        frame_counter_middle += 10
        frame_counter_top += 10
        
        if frame_counter_original % 10 == 0:
            current_frame_original = (current_frame_original + 1) % len(gif_images)
        if frame_counter_middle % 10 == 0:
            current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        if frame_counter_top % 10 == 0:
            current_frame_top = (current_frame_top + 1) % len(gif_images_top)
        
        # Highlight the currently selected button
        for i, button in enumerate(team_buttons):
            if i == selected_button_index:
                button.highlighted = True
            else:
                button.highlighted = False

        render_screen(screen, bg_image, gif_images, current_frame_original, gif_images_middle, current_frame_middle, gif_images_top, current_frame_top, team_buttons, using_keyboard, mouse_up)

    pygame.quit()

#Sub team menu
def create_trainer_buttons(screen, screen_width, screen_height, human_trainer, trainers, trainers_in_team, moves_dict, game_state):
    button_width, button_height = 400, 100
    button_spacing = 20
    total_button_height = (len(trainers_in_team) + 1) * button_height + len(trainers_in_team) * button_spacing
    start_y = (screen_height - total_button_height) / 2

    trainer_buttons = []
    for i, trainer in enumerate(trainers_in_team):
        button_y = start_y + i * (button_height + button_spacing)
        trainer_buttons.append(Button((screen_width - button_width) / 2, button_y, button_width, button_height, trainer.name.upper(), function=start_battle_with_trainer, params=[screen, human_trainer, trainer, moves_dict, game_state]))

    # Add a back button
    back_button_y = start_y + len(trainers_in_team) * (button_height + button_spacing)
    back_button = Button((screen_width - button_width) / 2, back_button_y, button_width, button_height, "BACK", function=battle_trainers_by_team_menu, params=[screen, human_trainer, trainers, moves_dict, game_state])
    trainer_buttons.append(back_button)

    return trainer_buttons

def sub_team_menu(screen, human_trainer, trainers, moves_dict, team_name, game_state):
    trainers_in_team = [trainer for trainer in trainers if trainer.team == team_name and trainer.name != human_trainer.name]
    
    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()

    # Initialize the frame counters and frame update counters
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
    frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0

    window_width, window_height = screen.get_size()
    buttons = create_trainer_buttons(screen, window_width, window_height, human_trainer, trainers, trainers_in_team, moves_dict, game_state)
    selected_button_index = 0
    using_keyboard = False

    running = True
    while running:
        running, using_keyboard, selected_button_index, mouse_up = handle_events(buttons, using_keyboard, selected_button_index)
        
        # Update GIF frames every 10 refreshes
        frame_counter_original += 10
        frame_counter_middle += 10
        frame_counter_top += 10
        
        if frame_counter_original % 10 == 0:
            current_frame_original = (current_frame_original + 1) % len(gif_images)
        if frame_counter_middle % 10 == 0:
            current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        if frame_counter_top % 10 == 0:
            current_frame_top = (current_frame_top + 1) % len(gif_images_top)
        
        # Highlight the currently selected button
        for i, button in enumerate(buttons):
            if i == selected_button_index:
                button.highlighted = True
            else:
                button.highlighted = False

        render_screen(screen, bg_image, gif_images, current_frame_original, gif_images_middle, current_frame_middle, gif_images_top, current_frame_top, buttons, using_keyboard, mouse_up)

    pygame.quit()

def battle_trainers_by_region_menu(screen, human_trainer, trainers, moves_dict, game_state):
    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()

    window_width, window_height = screen.get_size()
    button_width, button_height = 400, 100
    region_names = list(set([trainer.region for trainer in trainers if trainer.name != human_trainer.name]))

    # Calculate the horizontal center for the buttons
    button_x = (window_width - button_width) // 2

    # Create buttons for region selection
    region_buttons = []
    for i, region_name in enumerate(region_names, 1):
        button_y = 150 + i * 80  # Increase the vertical spacing here
        region_buttons.append(Button(button_x, button_y, button_width, button_height, region_name.upper(), function=sub_region_menu, params=[screen, human_trainer, trainers, moves_dict, region_name, game_state]))

    # Add a back button
    back_button = Button(button_x, 150 + len(region_names) * 105 + 100, button_width, button_height, "BACK", function=pre_battle_menu_pygame, params=[screen, game_state, human_trainer])
    region_buttons.append(back_button)  # Include the back button in the list for navigation

    selected_button_index = 0
    using_keyboard = False

    # Initialize the frame counters and frame update counters
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
    frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0

    # Sub-menu loop
    running = True
    while running:
        running, using_keyboard, selected_button_index, mouse_up = handle_events(region_buttons, using_keyboard, selected_button_index)

        # Update GIF frames
        frame_counter_original += 1
        frame_counter_middle += 1
        frame_counter_top += 1
        
        if frame_counter_original % 2 == 0:
            current_frame_original = (current_frame_original + 1) % len(gif_images)
        if frame_counter_middle % 2 == 0:
            current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        if frame_counter_top % 2 == 0:
            current_frame_top = (current_frame_top + 1) % len(gif_images_top)
        
        # Highlight the currently selected button
        for i, button in enumerate(region_buttons):
            if i == selected_button_index:
                button.highlighted = True
            else:
                button.highlighted = False

        render_screen(screen, bg_image, gif_images, current_frame_original, gif_images_middle, current_frame_middle, gif_images_top, current_frame_top, region_buttons, using_keyboard, mouse_up)

    pygame.quit()

def sub_region_menu(screen, human_trainer, trainers, moves_dict, region_name, game_state):
    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()

    window_width, window_height = screen.get_size()
    button_width, button_height = 400, 100
    sub_regions = get_sub_regions_by_region(region_name)
    button_x = (window_width - button_width) // 2  # Calculate the horizontal center for the buttons

    # Create buttons for sub-region selection
    sub_region_buttons = []
    for i, sub_region in enumerate(sub_regions, 1):
        button_y = 150 + i * 80
        sub_region_buttons.append(Button(button_x, button_y, button_width, button_height, sub_region.upper(), function=sub_region_trainer_menu, params=[screen, human_trainer, trainers, moves_dict, region_name, sub_region, game_state]))

    # Add a back button
    back_button_y = 150 + len(sub_regions) * 105 + 100
    back_button = Button(button_x, back_button_y, button_width, button_height, "BACK", function=pre_battle_menu_pygame, params=[screen, game_state, human_trainer])
    sub_region_buttons.append(back_button)  # Include the back button in the list for navigation

    selected_button_index = 0
    using_keyboard = False

    # Initialize the frame counters and frame update counters
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
    frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0

    # Sub-menu loop
    running = True
    while running:
        running, using_keyboard, selected_button_index, mouse_up = handle_events(sub_region_buttons, using_keyboard, selected_button_index)

        # Update GIF frames
        frame_counter_original += 1
        frame_counter_middle += 1
        frame_counter_top += 1
        
        if frame_counter_original % 10 == 0:
            current_frame_original = (current_frame_original + 1) % len(gif_images)
        if frame_counter_middle % 10 == 0:
            current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        if frame_counter_top % 10 == 0:
            current_frame_top = (current_frame_top + 1) % len(gif_images_top)

        # Highlight the currently selected button
        for i, button in enumerate(sub_region_buttons):
            if i == selected_button_index:
                button.highlighted = True
            else:
                button.highlighted = False

        render_screen(screen, bg_image, gif_images, current_frame_original, gif_images_middle, current_frame_middle, gif_images_top, current_frame_top, sub_region_buttons, using_keyboard, mouse_up)

    pygame.quit()

def sub_region_trainer_menu(screen, human_trainer, trainers, moves_dict, region_name, sub_region_name, game_state):
    # Load resources
    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()

    # Get screen size
    window_width, window_height = screen.get_size()
    button_width, button_height = 400, 100
    button_spacing = 20  # Define the spacing between buttons

    # Calculate the horizontal center for the buttons
    button_x = (window_width - button_width) // 2

    trainers_in_sub_region = [trainer for trainer in trainers if trainer.region == region_name and trainer.sub_region == sub_region_name]

    # Calculate the total height of buttons and spacing
    total_buttons_height = len(trainers_in_sub_region) * button_height + (len(trainers_in_sub_region) - 1) * button_spacing

    # Calculate the starting y position to center buttons vertically
    start_y = (window_height - total_buttons_height) // 2

    # Create buttons for trainer selection
    trainer_buttons = []
    for i, trainer in enumerate(trainers_in_sub_region, 1):
        button_y = start_y + (i - 1) * (button_height + button_spacing)
        trainer_buttons.append(Button(button_x, button_y, button_width, button_height, trainer.name.upper(), function=start_battle_with_trainer, params=[screen, human_trainer, trainer, moves_dict, game_state]))

    # Add a back button
    back_button_y = start_y + len(trainers_in_sub_region) * (button_height + button_spacing)
    back_button = Button(button_x, back_button_y, button_width, button_height, "BACK", function=pre_battle_menu_pygame, params=[screen, game_state, human_trainer])
    trainer_buttons.append(back_button)  # Include the back button in the list for navigation

    # Variables for keyboard navigation
    selected_button_index = 0
    using_keyboard = False

    # Initialize the frame counters for the GIF animations
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
    frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0

    # Sub-menu loop
    running = True
    while running:
        running, using_keyboard, selected_button_index, mouse_up = handle_events(trainer_buttons, using_keyboard, selected_button_index)

        # Update GIF frames periodically
        frame_counter_original += 1
        frame_counter_middle += 1
        frame_counter_top += 1
        
        if frame_counter_original % 10 == 0:
            current_frame_original = (current_frame_original + 1) % len(gif_images)
        if frame_counter_middle % 10 == 0:
            current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        if frame_counter_top % 10 == 0:
            current_frame_top = (current_frame_top + 1) % len(gif_images_top)

        # Highlight the currently selected button
        for i, button in enumerate(trainer_buttons):
            button.highlighted = (i == selected_button_index)

        # Render the screen with all elements
        render_screen(screen, bg_image, gif_images, current_frame_original, gif_images_middle, current_frame_middle, gif_images_top, current_frame_top, trainer_buttons, using_keyboard, mouse_up)

    pygame.quit()

def start_battle_with_trainer(screen, human_trainer, opponent_trainer, moves_dict, game_state):
    # Perform the battle logic here
    # For example, you can create an instance of the battle and start it
    
    opponent_trainer = deepcopy(opponent_trainer)
    battle = PygameBattle(game_state, human_trainer, opponent_trainer, moves_dict, human_trainer)
    battle.start()

"""def pre_battle_menu_pygame(screen, game_state, human_trainer):
    trainers = game_state['trainers']
    pokemons = game_state['pokemons']
    items = game_state['items']
    moves = game_state['moves']

    bg_image = pygame.image.load('pokemon_arena.jpg')
    bg_image = pygame.transform.scale(bg_image, (1280, 920))

    gif_frames = extract_and_save_gif_frames('anim_leaves.gif', 'frames')
    gif_images = [pygame.image.load(frame) for frame in gif_frames]
    gif_images_middle = [pygame.transform.scale(image, (image.get_width()*3, image.get_height()*3)) for image in gif_images]
    gif_images_top = [pygame.transform.flip(image, True, True) for image in gif_images[::-1]]

    current_frame_original = 0
    current_frame_middle = len(gif_images) // 3
    current_frame_top = 2 * len(gif_images) // 3
    frame_counter_original = 0
    frame_counter_middle = 0
    frame_counter_top = 0

    window_width, window_height = screen.get_size()
    button_width, button_height = 400, 100
    button_spacing = 20
    total_button_height = (4 * button_height) + (3 * button_spacing)
    start_y = (window_height - total_button_height) / 2

    battle_btn = Button((window_width - button_width) / 2, start_y, button_width, button_height, "BATTLE", function=choose_battle_menu_pygame, params=[screen, game_state, human_trainer, trainers, moves, pokemons])
    manage_btn = Button((window_width - button_width) / 2, start_y + button_height + button_spacing, button_width, button_height, "MANAGE", function=manage_menu_pygame, params=[screen, human_trainer, items, trainers, pokemons, game_state])
    options_btn = Button((window_width - button_width) / 2, start_y + 2 * (button_height + button_spacing), button_width, button_height, "OPTIONS", function=options_menu_pygame, params=[screen, game_state, human_trainer])
    exit_btn = Button((window_width - button_width) / 2, start_y + 3 * (button_height + button_spacing), button_width, button_height, "EXIT", function=exit_game)

    buttons = [battle_btn, manage_btn, options_btn, exit_btn]
    selected_button_index = 0
    using_keyboard = False

    running = True
    frame_counter = 0
    while running:
        mouse_up = False
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            if event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True
                using_keyboard = False
            if event.type == pygame.KEYDOWN:
                using_keyboard = True
                if event.key == pygame.K_DOWN:
                    selected_button_index = (selected_button_index + 1) % len(buttons)
                elif event.key == pygame.K_UP:
                    selected_button_index = (selected_button_index - 1) % len(buttons)
                elif event.key == pygame.K_RETURN:
                    buttons[selected_button_index].clicked = True
                    if buttons[selected_button_index].function:
                        if buttons[selected_button_index].params:
                            buttons[selected_button_index].function(*buttons[selected_button_index].params)
                        else:
                            buttons[selected_button_index].function()

        for i, button in enumerate(buttons):
            if i == selected_button_index:
                button.highlighted = True
            else:
                button.highlighted = False

        screen.blit(bg_image, (0, 0))
        screen.blit(gif_images[current_frame_original], (800, 600))
        screen.blit(gif_images_middle[current_frame_middle], (0, 0))
        screen.blit(gif_images_top[current_frame_top], (0, 0))

        frame_counter_original += 1
        frame_counter_middle += 1
        frame_counter_top += 1

        if frame_counter_original >= 2:
            current_frame_original = (current_frame_original + 1) % len(gif_images)
            frame_counter_original = 0
        if frame_counter_middle >= 2:
            current_frame_middle = (current_frame_middle + 1) % len(gif_images)
            frame_counter_middle = 0
        if frame_counter_top >= 2:
            current_frame_top = (current_frame_top + 1) % len(gif_images)
            frame_counter_top = 0

        for button in buttons:
            button.update(pygame.mouse.get_pos(), mouse_up, keyboard_navigation=using_keyboard)
            button.draw(screen)

        pygame.display.flip()
        pygame.time.Clock().tick(60)

    pygame.quit()
"""




    # Define the load_location_items function













def load_location_items_and_regions(filename='locations3.csv'):
    # Attempt to read the CSV file
    try:
        df = pd.read_csv(filename, delimiter=',', na_values=np.nan, keep_default_na=False)
    except pd.errors.ParserError as e:
        print(f"Error reading CSV file: {e}")
        return {}, {}, {}

    # Initialize dictionaries to store location data
    location_items = {}
    subregion_to_region = {}
    subregion_to_exits = {}

    # Process each row in the DataFrame
    for _, row in df.iterrows():
        sub_region = row['sub_region']
        region = row['region']
        items = row['items'].split('/') if isinstance(row['items'], str) else []

        # Parse exit data from the row
        exits = {
            'North': row['exitNorth'] if row['exitNorth'] else None,
            'East': row['exitEast'] if row['exitEast'] else None,
            'South': row['exitSouth'] if row['exitSouth'] else None,
            'West': row['exitWest'] if row['exitWest'] else None
        }

        # Debugging logs
        print(f"Loading subregion: {sub_region}, region: {region}")
        print(f"Items: {items}")
        print(f"Exits: {exits}")

        # Process and store item information
        location_items[sub_region] = {item.split(':')[0].strip(): float(item.split(':')[1]) for item in items if ':' in item}
        subregion_to_region[sub_region] = region
        subregion_to_exits[sub_region] = exits

    # Print final mapping of subregions to exits for debugging
    print(f"Subregion to Exits Mapping: {subregion_to_exits}")

    return location_items, subregion_to_region, subregion_to_exits

# Define the setup_environment function at the top level
def setup_environment(tmx_map, current_subregion, subregion_to_exits):
    # Define positions for fence tiles, high grass, and tall grass patches
    #fence_positions = [(100, 100 + i * 16, 0, 1) for i in range(50)]  # Example: A vertical line of fence tiles
    #high_grass_positions = [(150, 150 + i * 16, 0, 0) for i in range(10)]  # Example: A line of high grass tiles
    #tall_grass_positions = [(300, 300, 0, 0)]  # Example: A single tall grass patch
    #chest_position = (200, 600)  # Example: Position of a chest

    # Define the tall grass area (adjust the dimensions and position as needed)
    #tall_grass_area = pygame.Rect(300, 300, 100, 100)
    print(f"Setup Environment_Current subregion: {current_subregion}")

    # Initialize the house_colliders
    house_colliders = []
    

    # Search for the "House1" object group and create colliders
    if tmx_map and hasattr(tmx_map, 'objectgroups'):
        for obj_group in tmx_map.objectgroups:
            if obj_group.name.lower() == "house1":
                for obj in obj_group:
                    # Check if all necessary attributes are present
                    if hasattr(obj, 'x') and hasattr(obj, 'y') and hasattr(obj, 'width') and hasattr(obj, 'height'):
                        # Create a collider for each house object
                        house_collider = pygame.Rect(obj.x, obj.y, obj.width, obj.height)
                        house_colliders.append(house_collider)
                        print(f"Added house collider at ({obj.x}, {obj.y}, {obj.width}, {obj.height})")
                        print(f"House collider added: {house_collider}")

    
    # Initialize the door_collider
    door_collider = None

    # Search for the "doorgroup" object group and create a collider
    if tmx_map and hasattr(tmx_map, 'objectgroups'):
        for obj_group in tmx_map.objectgroups:
            if obj_group.name.lower() == "doorgroup":
                for obj in obj_group:
                    if hasattr(obj, 'x') and hasattr(obj, 'y') and hasattr(obj, 'width') and hasattr(obj, 'height'):
                        door_collider = pygame.Rect(obj.x, obj.y, obj.width, obj.height)
                        break  # Assuming there's only one door object.
    
    chest1_position = None  # Initialize chest1_position

    # Search for the "Chest1" object group and create a collider
    if tmx_map and hasattr(tmx_map, 'objectgroups'):
        for obj_group in tmx_map.objectgroups:
            if obj_group.name.lower() == "chest1":
                for obj in obj_group:
                    if hasattr(obj, 'x') and hasattr(obj, 'y') and hasattr(obj, 'width') and hasattr(obj, 'height'):
                        chest1_position = (obj.x, obj.y)
                        break  # Assuming there's only one "chest1" object.

    # In the setup_environment function...
    wild_grass_colliders = []

    if tmx_map and hasattr(tmx_map, 'objectgroups'):
        for obj_group in tmx_map.objectgroups:
            if obj_group.name.lower() == "wildgrass1":
                for obj in obj_group:
                    if hasattr(obj, 'x') and hasattr(obj, 'y') and hasattr(obj, 'width') and hasattr(obj, 'height'):
                        wild_grass_collider = pygame.Rect(obj.x, obj.y, obj.width, obj.height)
                        wild_grass_colliders.append(wild_grass_collider)


    # Initialize exit_colliders and exit_destinations
    # Initialize exit_colliders and exit_destinations
    # Initialize exit_colliders and exit_destinations

    # Initialize exit_colliders and exit_destinations
    exit_colliders = {}
    exit_destinations = {}

    # Handle exits from TMX map
    if tmx_map and hasattr(tmx_map, 'objectgroups'):
        for obj_group in tmx_map.objectgroups:
            if obj_group.name.lower() == "exits":
                for obj in obj_group:
                    if obj.name and hasattr(obj, 'x') and hasattr(obj, 'y') and hasattr(obj, 'width') and hasattr(obj, 'height'):
                        exit_collider = pygame.Rect(obj.x, obj.y, obj.width, obj.height)
                        # Ensure that the name is matched exactly as in the TMX file
                        exit_colliders[obj.name] = exit_collider

    # Populate exit_destinations
    exits = subregion_to_exits.get(current_subregion, {})
    for exit_name, collider in exit_colliders.items():
        # Map the exit name to the corresponding destination in the CSV file
        # Adjust the key to match the format used in the CSV (e.g., 'North', 'East')
        destination_subregion = exits.get(exit_name.replace("Exit", ""), None)
        if destination_subregion:
            exit_destinations[exit_name] = (collider, destination_subregion)
            print(f"Mapped {exit_name} to {destination_subregion}")
        else:
            print(f"No destination set for exit: {exit_name}")
            # Inside setup_environment function
            print(f"Current subregion: {current_subregion}")
            print(f"Available exits for this subregion in CSV: {subregion_to_exits.get(current_subregion, {})}")

    # Initialize NPC
    # Brock's object parameters



    # Base path for NPC sprite sheets
    base_npc_path = r"C:\Users\matth\OneDrive\PokePy\PokePyMain-main\sprites\peds"

    # Initialize NPCs

    # Initialize NPCs
    npcs = []

    # Base path for NPC sprite sheets
    base_npc_path = r"C:\Users\matth\OneDrive\PokePy\PokePyMain-main\sprites\peds"

    if tmx_map and hasattr(tmx_map, 'objectgroups'):
        for obj_group in tmx_map.objectgroups:
            if obj_group.name.lower() == "enemyspawngroup":
                for obj in obj_group:
                    if obj.name:  # Ensure that the NPC has a name
                        npc_name = obj.name  # Get the name of the NPC

                        # Construct the path to the sprite sheet using the NPC name
                        npc_sprite_sheet_path = os.path.join(base_npc_path, f"{npc_name}.png")

                        # Define the bounds for the NPC
                        npc_bounds = pygame.Rect(obj.x, obj.y, obj.width, obj.height)

                        # Create NPC with the extracted properties
                        npc = NPC(npc_sprite_sheet_path, (obj.x, obj.y), npc_bounds, animation_speed=20, trainer_name=npc_name)
                        npcs.append(npc)
                        print(f"Loaded NPC: {npc_name} at position ({obj.x}, {obj.y})")




    # Debugging: Print loaded colliders
    print("Loaded house colliders:", house_colliders)
    print("Loaded door collider:", door_collider)
    print("Loaded chest1 position:", chest1_position)
    print("Loaded wild grass colliders:", wild_grass_colliders)
    print("Loaded exit destinations:", exit_destinations)
    # Return all initialized variables and the NPCs    
    # In the setup_environment function
    # Debugging: Print loaded NPCs
    for npc in npcs:
        print(f"Loaded NPC: {npc.trainer_name} at position {npc.rect.topleft}")

    # At the end of setup_environment function
    return house_colliders, door_collider, chest1_position, wild_grass_colliders, exit_destinations, npcs

def load_tmx_map(tmx_file_path):
    print(f"Loading TMX map from: {tmx_file_path}")
    return load_pygame(tmx_file_path)

def render_map(screen, tmx_map):
    for layer in tmx_map.visible_layers:
        if isinstance(layer, pytmx.TiledTileLayer):
            for x, y, gid in layer:
                tile = tmx_map.get_tile_image_by_gid(gid)
                if tile:
                    # Create a copy of the tile surface for manipulation
                    tile_surface = pygame.Surface((tmx_map.tilewidth, tmx_map.tileheight), pygame.SRCALPHA)
                    tile_surface.blit(tile, (0, 0))

                    # Set the color key for transparency
                    tile_surface.set_colorkey((0, 0, 0))

                    # Blit the tile surface onto the screen
                    screen.blit(tile_surface, (x * tmx_map.tilewidth, y * tmx_map.tileheight))

def draw_high_grass_square(screen, start_x, start_y, width, height, get_tile_func):
    # Each tile in the sprite sheet is 8x8, but we're scaling them to 16x16
    tile_size = 16

    # Define the indices for the high grass tiles, assuming 0-based indexing
    top_left = (1, 0)
    top_middle = (2, 0)
    top_right = (3, 0)
    middle_left = (1, 1)  # B2
    center = (2, 1)  # C2 for the center
    middle_right = (3, 1)  # D2
    bottom_left = (1, 2)  # B3
    bottom_middle = (2, 2)  # C3 for the bottom
    bottom_right = (3, 2)  # D3

    for y in range(height):
        for x in range(width):
            # Determine the correct sprite based on the position
            if x == 0 and y == 0:  # Top-left corner
                tile = get_tile_func(*top_left)
            elif x == width - 1 and y == 0:  # Top-right corner
                tile = get_tile_func(*top_right)
            elif x == 0 and y == height - 1:  # Bottom-left corner
                tile = get_tile_func(*bottom_left)
            elif x == width - 1 and y == height - 1:  # Bottom-right corner
                tile = get_tile_func(*bottom_right)
            elif y == 0:  # Top edge
                tile = get_tile_func(*top_middle)
            elif y == height - 1:  # Bottom edge
                tile = get_tile_func(*bottom_middle)
            elif x == 0:  # Left edge
                tile = get_tile_func(*middle_left)
            elif x == width - 1:  # Right edge
                tile = get_tile_func(*middle_right)
            else:  # Center
                tile = get_tile_func(*center)

            # Blit the tile onto the screen at the correct position
            screen.blit(tile, (start_x + x * tile_size, start_y + y * tile_size))

    # Define the collision rectangle for the entire high grass area
    high_grass_collider = pygame.Rect(start_x, start_y, width * tile_size, height * tile_size)

    # Return the collision rectangle for use in collision detection
    return high_grass_collider
# New function to draw patches of tall grass
def draw_tall_grass_area(screen, tall_grass_area, get_tall_grass_tile):
    # Assuming each tile is 16x16 pixels
    tile_size = 16

    # Iterate over the area and draw tall grass tiles
    for y in range(tall_grass_area.top, tall_grass_area.bottom, tile_size):
        for x in range(tall_grass_area.left, tall_grass_area.right, tile_size):
            tall_grass_tile = get_tall_grass_tile(0, 0)  # Assuming (0, 0) is the tall grass tile in the sprite sheet
            screen.blit(tall_grass_tile, (x, y))





#OLD EXPLORE
def explore(screen, human_trainer, items, trainers, pokemons, game_state, moves_dict):
    global item_taken  # Add this line
    # Initialize variables
    chest_open = False  # Add this line to initialize chest_open
    item_taken = False  # Item taken state
    encounter_probability = 0.01  # Define the probability of encountering a wild Pokémon (e.g., 10%)

    # Initialize a dictionary to track the state of each chest
    chest_states = {
        'chest': False,  # False means not opened yet
        'chest1': False  # Add more chests as needed
    }

    # Create an instance of ConfirmationWindow
    # Inside explore function
    screen_width, screen_height = screen.get_size()
    window_width, window_height = 300, 250  # Width and height of the confirmation window
    window_x = (screen_width - window_width) // 2  # Center horizontally
    window_y = (screen_height - window_height) // 2  # Center vertically

    confirmation_window = ConfirmationWindow(window_x, window_y, window_width, window_height, "YOU FOUND AN ITEM!")


    pygame.joystick.init()  # Initialize the joystick module
    joystick_count = pygame.joystick.get_count()
    if joystick_count > 0:
        joystick = pygame.joystick.Joystick(0)  # Create a Joystick object for the first joystick
        joystick.init()
    else:
        joystick = None

    # Retrieve the current subregion from the game_state
    current_subregion = game_state.get('current_sub_region', 'default_sub_region')

    # Construct the file path for the TMX map based on the current subregion
    tmx_file_path = os.path.join('sprites', f'{current_subregion}.tmx')

    # Load the TMX map
    tmx_map = None
    try:
        tmx_map = load_tmx_map(tmx_file_path)
    except FileNotFoundError as e:
        print(f"Error loading TMX map for {current_subregion}: {e}")
        # Handle error (possibly exit, load a default map, or continue without a map)



    # Load resources and initialize settings
    def load_resources():
        base_sprites_path = os.path.join(os.path.dirname(__file__), 'sprites')
        paths = {
            'grass_tile': 'tilesets/grass.png',
            'character': 'characters/player.png',
            'mask': 'mapmask1.png',
            'fence_sheet': 'tilesets/fences.png',
            'high_grass_sheet': 'tilesets/highgrass.png',
            'tall_grass_sheet': 'tilesets/wildgrass.png',
            'chest_sheet': 'objects/chest_01.png'
        }
        resources = {}
        for key, path in paths.items():
            full_path = os.path.join(base_sprites_path, path)
            print(f"Loading {key}: {full_path}")
            if key != 'character':  # Load images for all except 'character'
                resources[key] = pygame.image.load(full_path)
            else:
                resources[key] = full_path  # Store the file path for the character sprite sheet
        resources['grass_tile'] = pygame.transform.scale(resources['grass_tile'], resources['grass_tile'].get_size())
        if 'mask' in resources:
            resources['mask'] = resources['mask'].convert_alpha()
        return resources

    def setup_collision_detection(mask_image):
        mask_colliders = [pygame.Rect(x, y, 1, 1) for x in range(mask_image.get_width()) for y in range(mask_image.get_height()) if mask_image.get_at((x, y)) != pygame.Color('black')]
        return mask_colliders

    def check_collision(mask, x, y, width, height):
        for dx in [0, width - 1]:
            for dy in [0, height - 1]:
                if mask.get_at((x + dx, y + dy)) != pygame.Color('black'):
                    return False
        return True
    
    # Load location_items
    # Load location items and the mapping of subregions to regions
    # Load exit data
    # Load location items and the mapping of subregions to regions and exits
    location_items, subregion_to_region, subregion_to_exits = load_location_items_and_regions()

    # Retrieve the current subregion from the game_state
    current_subregion = game_state.get('current_sub_region', 'default_sub_region')

    # Now call setup_environment with all the required arguments
    # fence_positions, high_grass_positions, tall_grass_positions, chest_position, tall_grass_area, house_colliders, door_collider, chest1_position, wild_grass_colliders, exit_destinations = setup_environment(tmx_map, current_subregion, subregion_to_exits)
    # house_colliders, door_collider, chest1_position, wild_grass_colliders, exit_destinations, npc = setup_environment(tmx_map, current_subregion, subregion_to_exits)
    # Inside explore function where setup_environment is called
    house_colliders, door_collider, chest1_position, wild_grass_colliders, exit_destinations, npcs = setup_environment(tmx_map, current_subregion, subregion_to_exits)
    print(f"ex Current Sub-Region: {current_subregion}")
    # Debugging: Print loaded colliders
    print("Loaded ex house colliders:", house_colliders)
    print("Loaded ex door collider:", door_collider)
    print("Loaded ex chest1 position:", chest1_position)
    print("Loaded ex wild grass colliders:", wild_grass_colliders)
    print("Loaded ex exit destinations:", exit_destinations)

    def select_item_for_chest(sub_region, location_items):
        if sub_region not in location_items:
            return None  # No items for this sub-region

        items_with_chances = location_items[sub_region]
        random_choice = random.random() * 100
        cumulative_chance = 0

        for item, chance in items_with_chances.items():
            cumulative_chance += chance
            if random_choice <= cumulative_chance:
                return item
        return None

    def flash_screen(screen, times, duration):
        for _ in range(times):
            screen.fill((0, 0, 0))  # Fill screen with black
            pygame.display.flip()
            pygame.time.delay(duration)

            screen.fill((255, 255, 255))  # Fill screen with white
            pygame.display.flip()
            pygame.time.delay(duration)

        # Fill the screen with black one last time to avoid a prolonged white screen
        screen.fill((0, 0, 0))
        pygame.display.flip()

    # Modify the create_collision_rects function to include chest1 collision rect
    """def create_collision_rects(fence_positions, chest_position, resources, chest1_position):
        collision_rects = []
        chest_collision_rect = None
        chest1_collision_rect = None  # Initialize chest1_collision_rect

        # Add collision rects for fence tiles
        for x, y, _, _ in fence_positions:
            collision_rects.append(pygame.Rect(x, y, 16, 16))

        # Add a collision rect for the chest and store it separately
        chest_collision_rect = pygame.Rect(chest_position[0], chest_position[1], 16, 16)
        collision_rects.append(chest_collision_rect)

        # Add a collision rect for chest1 and store it separately
        if chest1_position:
            chest1_collision_rect = pygame.Rect(chest1_position[0], chest1_position[1], 16, 16)
            collision_rects.append(chest1_collision_rect)

        return collision_rects, chest_collision_rect, chest1_collision_rect"""
    
    def create_collision_rects(house_colliders, door_collider, chest1_position):
        collision_rects = []

        # Initialize chest1_collision_rect to None
        chest1_collision_rect = None

        # Add each house and door collider to the collision rects
        collision_rects.extend(house_colliders)
        if door_collider:
            collision_rects.append(door_collider)

        # Add a collision rect for chest1 and store it separately
        if chest1_position:
            chest1_collision_rect = pygame.Rect(chest1_position[0], chest1_position[1], 16, 16)
            collision_rects.append(chest1_collision_rect)

        return collision_rects, chest1_collision_rect

    # Define interaction_rect at the beginning of the explore function
    interaction_rect = pygame.Rect(0, 0, 100, 100)  # Initial dummy values, will be updated

    def handle_input_and_events(character, game_state, keys, door_collider, pre_battle_menu_function, screen, trainers, pokemons, chest1_collision_rect, location_items, npcs, moves_dict, in_range_npc):
        global running, mouse_up, item_taken, chest_open, enter_pressed_last_frame
        nonlocal interaction_rect

        keys = pygame.key.get_pressed()

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            elif event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True
                print("Mouse button released")  # Debug line for mouse button release

        # Update and draw the confirmation window
        confirmation_window.update(pygame.mouse.get_pos(), mouse_up, keys)
        
        # Reset mouse_up flag after all updates
        mouse_up = False

        # If the confirmation window is visible, return early to lock other inputs
        if confirmation_window.visible:
            return


        # Update interaction_rect to the current position of the character
        interaction_rect = pygame.Rect(
            character.position[0] - 10, character.position[1] - 10,
            character.sprite_size[0] + 20, character.sprite_size[1] + 20
        )

        # Check for Enter key press near NPCs
        # Check for Enter key press near NPCs
        enter_pressed = keys[pygame.K_RETURN]
        if in_range_npc and keys[pygame.K_RETURN] and not enter_pressed_last_frame:
            for npc in npcs:
                if interaction_rect.colliderect(npc.rect):
                    print(f"Interacting with NPC: {npc.trainer_name}")
                    trainer_to_battle = next((trainer for trainer in trainers if trainer.name == npc.trainer_name), None)
                    if trainer_to_battle:
                        # Save the character's current position before the battle
                        game_state['saved_character_position'] = character.position.copy()
                        start_battle_with_trainer(screen, human_trainer, trainer_to_battle, moves_dict, game_state)
                        # After the battle, restore the character's position
                        character.position = game_state.get('saved_character_position')
                        character.rect.topleft = character.position
                        return  # Exit after starting and concluding the battle
                    else:
                        print(f"No trainer found for {npc.trainer_name}")

        # Check for Enter key press near the door collider
        if keys[pygame.K_RETURN] and door_collider and interaction_rect.colliderect(door_collider):
            # Check if the door_collider object has a name attribute and if it is "pokemart"
            if hasattr(door_collider, 'name') and door_collider.name.lower() == 'pokemart':
                print(f"pokemart door: {door_collider.name.lower()}")
                visit_pokemart_pygame(screen, human_trainer, items, pre_battle_menu_function, game_state)
            else:
                visit_pokecenter_pygame(human_trainer, pre_battle_menu_function, screen, game_state, trainers, pokemons)


        # Check for Enter key press near chest1
        # Check for Enter key press near chest1
        if keys[pygame.K_RETURN] and interaction_rect.colliderect(chest1_collision_rect):
            interaction_rect = pygame.Rect(
                character.position[0] - 10, character.position[1] - 10,
                character.sprite_size[0] + 20, character.sprite_size[1] + 20
            )

            # Handle interaction with chest1
            if interaction_rect.colliderect(chest1_collision_rect):
                if not chest_states['chest1']:  # Check if chest1 is not opened
                    chest_open = True
                    sub_region = game_state.get('current_sub_region', 'default_sub_region')
                    item_name = select_item_for_chest(sub_region, location_items)
                    if item_name and item_name in items:
                        item = copy.deepcopy(items[item_name])
                        human_trainer.add_item(item)
                        item_taken = True
                        chest_states['chest1'] = True
                        confirmation_window.open_window(f"YOU FOUND A\n{item_name.upper()}!")
                        print(f"You found a {item_name}!")
                    else:
                        print("Chest1 is empty or item not found.")
                        confirmation_window.open_window("THE CHEST IS EMPTY!")  # Show a confirmation window for empty chest
                else:
                    print("Chest1 empty!")
                    confirmation_window.open_window("THE CHEST IS EMPTY!")  # Show a confirmation window for empty chest

        enter_pressed_last_frame = enter_pressed

    # Modify the handle_input_and_events function to include chest1 interaction
    """def handle_input_and_events(character, chest_collision_rect, game_state, keys, door_collider, pre_battle_menu_function, screen, trainers, pokemons, chest1_collision_rect, location_items):
        global running, mouse_up, item_taken, chest_open
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            elif event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True

        # Check for Enter key press
        # Check for Enter key press near the chest
        if keys[pygame.K_RETURN]:
            interaction_rect = pygame.Rect(
                character.position[0] - 10, character.position[1] - 10,
                character.sprite_size[0] + 20, character.sprite_size[1] + 20
            )

            # Handle interaction with chest
            if interaction_rect.colliderect(chest_collision_rect):
                if not chest_states['chest']:  # Check if chest is not opened
                    chest_open = True
                    item = copy.deepcopy(items.get('Potion'))
                    if item:
                        human_trainer.add_item(item)
                        item_taken = True
                        chest_states['chest'] = True  # Update chest state to opened
                        print("You found a Potion!")
                    else:
                        print("Potion not found in items list")
                else:
                    print("Chest empty!")  # Chest already opened

            # Handle interaction with chest1
            # Handle interaction with chest1
            if interaction_rect.colliderect(chest1_collision_rect):
                if not chest_states['chest1']:  # Check if chest1 is not opened
                    chest_open = True
                    sub_region = game_state.get('current_sub_region', 'default_sub_region')  # Get the current sub-region from game_state
                    item_name = select_item_for_chest(sub_region, location_items)  # Use the new function
                    if item_name and item_name in items:
                        item = copy.deepcopy(items[item_name])
                        human_trainer.add_item(item)
                        item_taken = True
                        chest_states['chest1'] = True
                        print(f"You found a {item_name}!")
                    else:
                        print("Chest1 is empty or item not found.")
                else:
                    print("Chest1 empty!")
            
        # Check for Enter key press near the door
        interaction_rect = pygame.Rect(
            character.position[0] - 10, character.position[1] - 10,
            character.sprite_size[0] + 20, character.sprite_size[1] + 20
        )
        if keys[pygame.K_RETURN] and door_collider and interaction_rect.colliderect(door_collider):
            visit_pokecenter_pygame(human_trainer, pre_battle_menu_function, screen, game_state, trainers, pokemons)"""

    def update_game_state(character, collision_rects, mask_colliders, dt, resources, encounter_probability, game_state, keys, wild_grass_colliders, exit_destinations, house_colliders, door_collider, chest1_collision_rect, npcs, joystick=None, source_map=None):
        # Function implementation...
        global mouse_up, chest_open, item_taken, running
        new_destination = None  # Initialize new_destination here

        # Debugging: Print details when a collision occurs
        def debug_collision(collider, name):
            if character.rect.colliderect(collider):
                print(f"Character collided with {name} at {collider}")

        for house_collider in house_colliders:
            debug_collision(house_collider, "House")

        if door_collider:
            debug_collision(door_collider, "Door")
            
        # Existing logic for checking in wild grass
        in_wild_grass = any(character.rect.colliderect(wild_grass_collider) for wild_grass_collider in wild_grass_colliders)

        if in_wild_grass:
            # Slow down the character by 50% when in wild grass
            adjusted_dt = dt * 0.50

            # Wild Pokémon encounter logic for wild grass
            if random.random() < encounter_probability:
                current_subregion = game_state.get('current_sub_region', 'default_sub_region')
                current_region = subregion_to_region.get(current_subregion, 'default_region')

                flash_screen(screen, 2, 150)  # Flash 2 times with 150ms per color

                game_state['saved_character_position'] = character.position.copy()
                human_trainer.battle_wild_pokemon(current_region, current_subregion, pokemons, game_state)
            
                character.position = game_state.get('saved_character_position')
                character.rect.topleft = character.position
        else:
            adjusted_dt = dt
        

        for npc_object in npcs:
            # Add each NPC's collider to the collision checks
            collision_rects.append(npc_object.rect)
            # Update each NPC's state, providing the player's rect for collision detection
            npc_object.update(character.rect)

        # Existing logic for updating character
        character.update(keys, collision_rects, adjusted_dt, joystick)
        
        # Debugging: Check for collision with house colliders
        for house_collider in house_colliders:
            if character.rect.colliderect(house_collider):
                print(f"Character collided with house at {house_collider}")

        # Check for collision with the door collider and exit colliders
        # Now door_collider is accessible within this function
        # Check for collision with the door collider and exit colliders
        # Check for collision with the door collider and exit colliders
        # Check for collision with the door collider and exit colliders
        if door_collider and character.rect.colliderect(door_collider):
            print("Collided with door collider")
            print(f"door colliding with: {door_collider}")

        new_tmx_map = None
        new_destination = None

        # Ensure source_map is correctly set to the current map
        source_map = game_state.get('current_sub_region', None)

        for exit_name, (collider, destination) in exit_destinations.items():
            if character.rect.colliderect(collider):
                print(f"Collided with {exit_name}, transitioning from {source_map} to {destination}")
                new_tmx_file_path = os.path.join('sprites', f'{destination}.tmx')
                new_tmx_map = load_tmx_map(new_tmx_file_path)
                new_destination = destination
                break

        # Only perform the following steps when there is an actual map transition
        if new_tmx_map:
            # Perform the transition to the new map
            print(f"Transitioning to new TMX map: {new_destination}")
            game_state['tmx_map'] = new_tmx_map
            game_state['current_sub_region'] = new_destination

            # Clear existing data for transition
            npcs.clear()
            house_colliders.clear()
            wild_grass_colliders.clear()
            exit_destinations.clear()

            current_subregion = new_destination

            # Reinitialize environment for the new map
            house_colliders, door_collider, chest1_position, wild_grass_colliders, exit_destinations, new_npcs = setup_environment(new_tmx_map, new_destination, subregion_to_exits)
            npcs.extend(new_npcs)

            print(f"new same npcs: {npcs}")
            print(f"new npcs: {new_npcs}")

            print(f"1New house colliders: {house_colliders}")
            print(f"1New door collider: {door_collider}")
            print(f"1New exit destinations: {exit_destinations}")

            # Update collision rects with the new environment
            collision_rects.clear()  # Clear existing collision rects
            collision_rects, chest1_collision_rect = create_collision_rects(house_colliders, door_collider, chest1_position)


            # Reload the environment for the new subregion
            print("Re-initializing colliders and exit destinations for new map.")
            house_colliders, door_collider, chest1_position, wild_grass_colliders, exit_destinations, npcs = setup_environment(new_tmx_map, new_destination, subregion_to_exits)

            print(f"2New house colliders: {house_colliders}")
            print(f"2New door collider: {door_collider}")
            print(f"2New exit destinations: {exit_destinations}")
            # Update collision rects with the new environment
            collision_rects, chest1_collision_rect = create_collision_rects(house_colliders, door_collider, chest1_position)

            # Determine the appropriate spawn location based on the exit used
            exit_to_spawn_mapping = {
                'ExitNorth': 'SpawnSouth',
                'ExitSouth': 'SpawnNorth',
                'ExitEast': 'SpawnWest',
                'ExitWest': 'SpawnEast'
            }

            spawn_group_name = exit_to_spawn_mapping.get(exit_name, "SpawnNorth")  # Default spawn location

            spawn_position = None
            if hasattr(new_tmx_map, 'objectgroups'):
                for obj_group in new_tmx_map.objectgroups:
                    if obj_group.name.lower() == "spawnspot":
                        for obj in obj_group:
                            if obj.name.lower() == spawn_group_name.lower():
                                spawn_position = (obj.x, obj.y)
                                break
                            if spawn_position:
                                break
            print(f"3New house colliders: {house_colliders}")
            print(f"3New door collider: {door_collider}")
            print(f"3New exit destinations: {exit_destinations}")

            if spawn_position:
                character.position = spawn_position
                character.rect.topleft = character.position
                


        # Reset mouse_up flag at the end of each update cycle
        mouse_up = False
        # Return new_tmx_map for checking in the main loop
        return new_tmx_map, new_destination
    

    """def render_game(screen, resources, character, fence_positions, high_grass_positions, tall_grass_positions, chest_position, chest_open, exit_button, mouse_pos, mouse_up, tmx_map):
        # Clear the screen
        screen.fill((0, 0, 0))  # Fill with a background color, if needed

        render_map(screen, tmx_map)

        # Render TMX map as background if it's available
        # if tmx_map:
        #     render_map(screen, tmx_map)
        # else:
        #     # Fallback: Render grass tiles if TMX map is not available
        #     grass_tile = resources['grass_tile']
        #     screen_width, screen_height = screen.get_size()
        #     tile_width, tile_height = grass_tile.get_size()
        #     for y in range(0, screen_height, tile_height):
        #         for x in range(0, screen_width, tile_width):
        #             screen.blit(grass_tile, (x, y))

        # Draw fence tiles
        fence_sheet = resources['fence_sheet']
        for x, y, col, row in fence_positions:
            fence_tile = fence_sheet.subsurface(col * 16, row * 16, 16, 16)
            screen.blit(fence_tile, (x, y))

        # Function to get a specific high grass tile from the high grass sheet
        def get_high_grass_tile(col, row):
            return resources['high_grass_sheet'].subsurface(col * 16, row * 16, 16, 16)

        # Function to get a specific tall grass tile from the tall grass sheet
        def get_tall_grass_tile(col, row):
            return resources['tall_grass_sheet'].subsurface(col * 16, row * 16, 16, 16)

        # Draw high grass square
        high_grass_collider = draw_high_grass_square(screen, 500, 500, 25, 5, get_high_grass_tile)
        # Add high grass collider to collision rects if needed

        # Draw tall grass area
        draw_tall_grass_area(screen, tall_grass_area, get_tall_grass_tile)


        # Draw the chest
        chest_sheet = resources['chest_sheet']
        chest_tile = chest_sheet.subsurface(0 if not chest_open else 16, 0, 16, 16)
        screen.blit(chest_tile, chest_position)

        # Draw the character
        character.draw(screen)

        # Update and draw the exit button
        exit_button.update(mouse_pos, mouse_up)
        exit_button.draw(screen)

        # Update the display
        pygame.display.flip()"""

    """def render_game(screen, tmx_map, character, npcs, interaction_rect):
        screen.fill((0, 0, 0))  # Clear the screen
        render_map(screen, tmx_map)  # Render the TMX map
        character.draw(screen)  # Draw the character
        #exit_button.draw(screen)

        # Initialize the interaction flag
        in_range_npc = False

        # Iterate through NPCs to draw them and check for collision
        for npc in npcs:
            #print(f"Drawing NPC: {npc.trainer_name}, Position: {npc.rect.topleft}")  # Debug print
            npc.update(character.rect)
            npc.draw(screen)

            # Check for collision and set color accordingly
            if interaction_rect.colliderect(npc.rect):
                in_range_npc = True  # Set the flag if interaction rectangle collides with NPC
                rect_color_npc = (0, 255, 0)  # Green for NPC rect if colliding
                rect_color_interaction = (255, 0, 0)  # Red for interaction rect if colliding
                #in_range_npc = True  # Set the interaction flag to True
            else:
                rect_color_npc = (255, 255, 0)  # Yellow for NPC rect if not colliding
                rect_color_interaction = (0, 0, 255)  # Blue for interaction rect if not colliding

            # Draw the NPC and interaction rectangles with the determined colors
            pygame.draw.rect(screen, rect_color_npc, npc.rect, 2)
            pygame.draw.rect(screen, rect_color_interaction, interaction_rect, 2)

        # Handle NPC interaction logic here based on the in_range_npc flag
        #if in_range_npc:
            #print("Interacting with an NPC")

        pygame.display.flip()  # Update the display
        return in_range_npc  # Return the flag indicating if player is in range of an NPC"""


    def render_game(screen, tmx_map, character, npcs, interaction_rect, confirmation_window, exit_button):
        # First, render everything to a temporary surface
        temp_surface = pygame.Surface(screen.get_size())
        temp_surface.fill((0, 0, 0))  # Clear the temp surface
        render_map(temp_surface, tmx_map)  # Render the TMX map onto the temp surface
        character.draw(temp_surface)  # Draw the character onto the temp surface

        # Calculate the rectangle area around the player for the zoom effect
        zoom_rect_width, zoom_rect_height = 640, 480
        zoom_rect = pygame.Rect(
            character.position[0] - zoom_rect_width // 2, 
            character.position[1] - zoom_rect_height // 2, 
            zoom_rect_width, 
            zoom_rect_height
        )

        # Clamp the rectangle to ensure it doesn't go outside the map boundaries
        zoom_rect.clamp_ip(temp_surface.get_rect())

        # Update NPCs and check for interactions
        in_range_npc = False
        for npc in npcs:
            npc.update(character.rect)
            # Draw NPCs onto the temp surface
            npc.draw(temp_surface)
            # Check for collision with the interaction rect (adjusted for zoom)
            zoomed_interaction_rect = interaction_rect.move(-zoom_rect.left, -zoom_rect.top)
            if zoomed_interaction_rect.colliderect(npc.rect):
                in_range_npc = True

        # Capture the portion of the temp surface
        captured_area = temp_surface.subsurface(zoom_rect)

        # Scale this captured area to a larger size for the zoom effect
        zoom_scale = 2  # Adjust this value to control the zoom level
        zoomed_area = pygame.transform.scale(captured_area, (zoom_rect_width * zoom_scale, zoom_rect_height * zoom_scale))

        # Now, clear the main screen and blit the zoomed area onto it
        screen.fill((0, 0, 0))  # Clear the main screen
        screen.blit(zoomed_area, (0, 0))  # Blit the zoomed area onto the main screen

        # Draw a purple rectangle around the zoomed area on the main screen
        purple = (128, 0, 128)  # RGB for purple
        pygame.draw.rect(screen, purple, (0, 0, zoom_rect_width * zoom_scale, zoom_rect_height * zoom_scale), 2)

        # Draw the confirmation window if it is visible
        if confirmation_window.visible:
            confirmation_window.draw(screen)

        # Draw the exit button
        exit_button.draw(screen)

        # Update the display
        pygame.display.flip()
        return in_range_npc  # Return the flag indicating if player is in range of an NPC

    def return_to_pre_battle_menu(screen, updated_game_state):
        human_trainer = updated_game_state.get('human_trainer')
        if human_trainer:
            pre_battle_menu_pygame(screen, updated_game_state, human_trainer)
        else:
            print("Error: human_trainer not found in updated_game_state")

    # Modify the function associated with the exit button
    def exit_and_save_position():
        # Save the character's current position to the game_state
        game_state['saved_character_position'] = character.position.copy()
        # Call the function to return to the pre-battle menu
        return_to_pre_battle_menu(screen, game_state)

    # Create the exit button with the updated function
    exit_button = Button(1060, 800, 200, 100, text="EXIT", function=exit_and_save_position)

    #print(f"Loop New house colliders: {house_colliders}")
    #print(f"Loop New door collider: {door_collider}")
    #print(f"Loop New exit destinations: {exit_destinations}")

    resources = load_resources()
    mask_colliders = setup_collision_detection(resources['mask'])
    screen_width, screen_height = screen.get_size()
    clock = pygame.time.Clock()

    # Initialize the character
    character = Character(resources['character'], (48, 48), 6, 10)
    saved_position = game_state.get('saved_character_position', [screen_width // 2 - character.sprite_size[0] // 2, screen_height // 2 - character.sprite_size[1] // 2])
    character.position = saved_position
    character.rect.topleft = character.position

    # Environment setup
    # fence_positions, high_grass_positions, tall_grass_positions, chest_position, tall_grass_area, house_colliders, door_collider, chest1_position = setup_environment(tmx_map)
    # fence_positions, high_grass_positions, tall_grass_positions, chest_position, tall_grass_area, house_colliders, door_collider, chest1_position, wild_grass_colliders, exit_collider = setup_environment(tmx_map, current_subregion, subregion_to_exits)

    # In the explore function
    # In the explore function
    # collision_rects, chest_collision_rect, chest1_collision_rect = create_collision_rects(fence_positions, chest_position, resources, chest1_position)

    # Inside explore function
    # Call setup_environment to initialize the environment
    house_colliders, door_collider, chest1_position, wild_grass_colliders, exit_destinations, npc = setup_environment(tmx_map, current_subregion, subregion_to_exits)
    print(f"ex2 Current Sub-Region: {current_subregion}")
        # Debugging: Print loaded colliders
    print("Loaded ex2 house colliders:", house_colliders)
    print("Loaded ex2 door collider:", door_collider)
    print("Loaded ex2 chest1 position:", chest1_position)
    print("Loaded ex2 wild grass colliders:", wild_grass_colliders)
    print("Loaded ex2 exit destinations:", exit_destinations)
    
    collision_rects, chest1_collision_rect = create_collision_rects(house_colliders, door_collider, chest1_position)


    # Add each house and door collider to the collision rects
    for house_collider in house_colliders:
        collision_rects.append(house_collider)
    if door_collider:
        collision_rects.append(door_collider)

    # Function to get a specific high grass tile from the high grass sheet
    # def get_high_grass_tile(col, row):
    #     return resources['high_grass_sheet'].subsurface(col * 16, row * 16, 16, 16)

    # Draw high grass square and get its collider
    # high_grass_collider = draw_high_grass_square(screen, 500, 500, 25, 5, get_high_grass_tile)

    # Add high grass collider to collision rects
    # collision_rects.append(high_grass_collider)


    current_map = game_state.get('tmx_map', 'test2.tmx')  # Assuming 'test2.tmx' is the default map
        
    # Main loop
    running = True
    # Main loop in the explore function
    while running:
        dt = clock.tick(60) / 1000
        mouse_pos = pygame.mouse.get_pos()
        mouse_up = False
        keys = pygame.key.get_pressed()

        # Check for joystick events if a joystick is connected
        if joystick:
            joystick_x_axis = joystick.get_axis(0)  # Left-right (typically the X-axis)
            joystick_y_axis = joystick.get_axis(1)  # Up-down (typically the Y-axis)


        # Handle input events
        #handle_input_and_events(character, chest_collision_rect, game_state, keys, door_collider, pre_battle_menu_pygame, screen, trainers, pokemons, chest1_collision_rect, location_items)
        #handle_input_and_events(character, game_state, keys, door_collider, pre_battle_menu_pygame, screen, trainers, pokemons, chest1_collision_rect, location_items, npc, moves_dict)

        # Update game state with joystick input
        # update_game_state(character, collision_rects, mask_colliders, dt, resources, tall_grass_area, encounter_probability, game_state, keys, joystick)  # Pass joystick object
        # update_game_state(character, collision_rects, mask_colliders, dt, resources, tall_grass_area, encounter_probability, game_state, keys, wild_grass_colliders, exit_collider, joystick)        # Render the game
        # Inside the explore function, find the call to update_game_state and update it
        # Pass door_collider to update_game_state
        # update_game_state(character, collision_rects, mask_colliders, dt, resources, encounter_probability, game_state, keys, wild_grass_colliders, exit_destinations, door_collider, joystick)
        
        # Update the TMX map if there is a transition to a new map
        # if 'new_tmx_map' in game_state and game_state['new_tmx_map']:
        #     tmx_map = game_state['new_tmx_map']
        #     game_state['tmx_map'] = tmx_map
        #     del game_state['new_tmx_map']  # Remove the temporary key
        
        # Receive new_tmx_map from update_game_state
        new_tmx_map, new_destination  = update_game_state(character, collision_rects, mask_colliders, dt, resources, encounter_probability, game_state, keys, wild_grass_colliders, exit_destinations, house_colliders, door_collider, chest1_collision_rect, npcs, joystick, current_map)


        if new_tmx_map:
            # Transition to the new map and setup environment
            tmx_map = new_tmx_map
            current_subregion = new_destination  # Update the current_subregion to match the new map
            house_colliders, door_collider, chest1_position, wild_grass_colliders, exit_destinations, npcs = setup_environment(tmx_map, current_subregion, subregion_to_exits)
            print(f"new tmx Current Sub-Region: {current_subregion}")
            collision_rects, chest1_collision_rect = create_collision_rects(house_colliders, door_collider, chest1_position)
            game_state['tmx_map'] = tmx_map
            game_state['current_sub_region'] = current_subregion  # Update the game state's subregion



        # Inside your game loop where you call update_game_state
        #print(f"Loop New house colliders: {house_colliders}")
        #print(f"Loop New door collider: {door_collider}")
        #print(f"Loop New exit destinations: {exit_destinations}")
        #update_game_state(character, collision_rects, mask_colliders, dt, resources, encounter_probability, game_state, keys, wild_grass_colliders, exit_destinations, house_colliders, door_collider, chest1_collision_rect, npcs, joystick, current_map)
        # Update the current map
        #print(f"Loop5 New house colliders: {house_colliders}")
        #print(f"Loop5 New door collider: {door_collider}")
        #print(f"Loop5 New exit destinations: {exit_destinations}")
        # tmx_map = game_state.get('tmx_map', tmx_map)
        #print(f"TMX: {tmx_map}")
        
        # render_game(screen, resources, character, fence_positions, high_grass_positions, tall_grass_positions, chest_position, chest_open, exit_button, mouse_pos, mouse_up, tmx_map)
        #render_game(screen, tmx_map, character, npcs, interaction_rect)
        # Inside the main game loop
        interaction_rect = pygame.Rect(character.position[0] - 10, character.position[1] - 10, character.sprite_size[0] + 20, character.sprite_size[1] + 20)

        in_range_npc = render_game(screen, tmx_map, character, npcs, interaction_rect, confirmation_window, exit_button)
        
        # Update and draw the confirmation window
        # Inside the main game loop

        # Update and draw the confirmation window
        # Update and draw the confirmation window
        # confirmation_window.update(pygame.mouse.get_pos(), mouse_up, keys)
        # if confirmation_window.visible:
        #     confirmation_window.draw(screen)

        # Reset mouse_up flag after all updates
        # mouse_up = False

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            elif event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True  # Set mouse_up to True when mouse button is released

        # Update and draw the exit button
        exit_button.update(mouse_pos, mouse_up)
        # exit_button.draw(screen)

        confirmation_window.update(pygame.mouse.get_pos(), mouse_up, keys)
 
        handle_input_and_events(character, game_state, keys, door_collider, pre_battle_menu_pygame, screen, trainers, pokemons, chest1_collision_rect, location_items, npcs, moves_dict, in_range_npc)

        # Reset mouse_up flag after updating the button
        mouse_up = False

        # Update the display
        pygame.display.flip()

    # Update the game state before returning
    game_state['human_trainer'] = human_trainer
    return game_state







#NEW EXPLORE
"""def flash_screen(screen, times, duration):
    for _ in range(times):
        screen.fill((0, 0, 0))  # Fill screen with black
        pygame.display.flip()
        pygame.time.delay(duration)

        screen.fill((255, 255, 255))  # Fill screen with white
        pygame.display.flip()
        pygame.time.delay(duration)

    # Fill the screen with black one last time to avoid a prolonged white screen
    screen.fill((0, 0, 0))
    pygame.display.flip()

def explore_load_resources():
    base_sprites_path = os.path.join(os.path.dirname(__file__), 'sprites')
    paths = {
        'grass_tile': 'tilesets/grass.png',
        'character': 'characters/player.png',
        'mask': 'mapmask1.png',
        'fence_sheet': 'tilesets/fences.png',
        'high_grass_sheet': 'tilesets/highgrass.png',
        'tall_grass_sheet': 'tilesets/wildgrass.png',
        'chest_sheet': 'objects/chest_01.png'
    }
    resources = {}
    for key, path in paths.items():
        full_path = os.path.join(base_sprites_path, path)
        print(f"Loading {key}: {full_path}")
        if key != 'character':  # Load images for all except 'character'
            resources[key] = pygame.image.load(full_path)
        else:
            resources[key] = full_path  # Store the file path for the character sprite sheet
    resources['grass_tile'] = pygame.transform.scale(resources['grass_tile'], resources['grass_tile'].get_size())
    if 'mask' in resources:
        resources['mask'] = resources['mask'].convert_alpha()
    return resources

def setup_collision_detection(mask_image):
    mask_colliders = [pygame.Rect(x, y, 1, 1) for x in range(mask_image.get_width()) for y in range(mask_image.get_height()) if mask_image.get_at((x, y)) != pygame.Color('black')]
    return mask_colliders

def load_subregion_map(game_state):
    current_subregion = game_state.get('current_sub_region', 'default_sub_region')
    tmx_file_path = os.path.join('sprites', f'{current_subregion}.tmx')
    try:
        return load_tmx_map(tmx_file_path), current_subregion
    except FileNotFoundError as e:
        print(f"Error loading TMX map for {current_subregion}: {e}")
        return None, current_subregion

def handle_input_and_events(character, game_state, keys, door_collider, pre_battle_menu_function, screen, trainers, pokemons, chest1_collision_rect, location_items, npcs, moves_dict, in_range_npc):
    global running, mouse_up, item_taken, chest_open, enter_pressed_last_frame
    nonlocal interaction_rect


    for event in pygame.event.get():
        if event.type == pygame.QUIT:
            running = False
        elif event.type == pygame.MOUSEBUTTONUP:
            mouse_up = True

    # Update interaction_rect to the current position of the character
    interaction_rect = pygame.Rect(
        character.position[0] - 10, character.position[1] - 10,
        character.sprite_size[0] + 20, character.sprite_size[1] + 20
    )

    # Check for Enter key press near NPCs
    # Check for Enter key press near NPCs
    enter_pressed = keys[pygame.K_RETURN]
    if in_range_npc and enter_pressed and not enter_pressed_last_frame:
        for npc in npcs:
            if interaction_rect.colliderect(npc.rect):
                print(f"Interacting with NPC: {npc.trainer_name}")
                trainer_to_battle = next((trainer for trainer in trainers if trainer.name == npc.trainer_name), None)
                if trainer_to_battle:
                    # Save the character's current position before the battle
                    game_state['saved_character_position'] = character.position.copy()
                    start_battle_with_trainer(screen, human_trainer, trainer_to_battle, moves_dict, game_state)
                    # After the battle, restore the character's position
                    character.position = game_state.get('saved_character_position')
                    character.rect.topleft = character.position
                    return  # Exit after starting and concluding the battle
                else:
                    print(f"No trainer found for {npc.trainer_name}")

    # Check for Enter key press near the door collider
    if keys[pygame.K_RETURN] and door_collider and interaction_rect.colliderect(door_collider):
        # Check if the door_collider object has a name attribute and if it is "pokemart"
        if hasattr(door_collider, 'name') and door_collider.name.lower() == 'pokemart':
            print(f"pokemart door: {door_collider.name.lower()}")
            visit_pokemart_pygame(screen, human_trainer, items, pre_battle_menu_function, game_state)
        else:
            visit_pokecenter_pygame(human_trainer, pre_battle_menu_function, screen, game_state, trainers, pokemons)

    # Check for Enter key press near chest1
    if keys[pygame.K_RETURN] and interaction_rect.colliderect(chest1_collision_rect):
        # [Handle interaction with chest1...]
        interaction_rect = pygame.Rect(
            character.position[0] - 10, character.position[1] - 10,
            character.sprite_size[0] + 20, character.sprite_size[1] + 20
        )

        # Handle interaction with chest1
        if interaction_rect.colliderect(chest1_collision_rect):
            if not chest_states['chest1']:  # Check if chest1 is not opened
                chest_open = True
                sub_region = game_state.get('current_sub_region', 'default_sub_region')  # Get the current sub-region from game_state
                item_name = select_item_for_chest(sub_region, location_items)  # Use the new function
                if item_name and item_name in items:
                    item = copy.deepcopy(items[item_name])
                    human_trainer.add_item(item)
                    item_taken = True
                    chest_states['chest1'] = True
                    print(f"You found a {item_name}!")
                else:
                    print("Chest1 is empty or item not found.")
            else:
                print("Chest1 empty!")
    enter_pressed_last_frame = enter_pressed


    # Check for Enter key press near NPC
    # Check for Enter key press near NPC
    # Check for Enter key press near NPCs
    # Check for Enter key press near NPCs

def update_game_state(character, collision_rects, mask_colliders, dt, resources, encounter_probability, game_state, keys, wild_grass_colliders, exit_destinations, house_colliders, door_collider, chest1_collision_rect, npcs, joystick=None, source_map=None):
    # Function implementation...
    global mouse_up, chest_open, item_taken, running
    new_destination = None  # Initialize new_destination here

    # Debugging: Print details when a collision occurs
    def debug_collision(collider, name):
        if character.rect.colliderect(collider):
            print(f"Character collided with {name} at {collider}")

    for house_collider in house_colliders:
        debug_collision(house_collider, "House")

    if door_collider:
        debug_collision(door_collider, "Door")
        
    # Existing logic for checking in wild grass
    in_wild_grass = any(character.rect.colliderect(wild_grass_collider) for wild_grass_collider in wild_grass_colliders)

    if in_wild_grass:
        # Slow down the character by 50% when in wild grass
        adjusted_dt = dt * 0.50

        # Wild Pokémon encounter logic for wild grass
        if random.random() < encounter_probability:
            current_subregion = game_state.get('current_sub_region', 'default_sub_region')
            current_region = subregion_to_region.get(current_subregion, 'default_region')

            flash_screen(screen, 2, 150)  # Flash 2 times with 150ms per color

            game_state['saved_character_position'] = character.position.copy()
            human_trainer.battle_wild_pokemon(current_region, current_subregion, pokemons, game_state)
        
            character.position = game_state.get('saved_character_position')
            character.rect.topleft = character.position
    else:
        adjusted_dt = dt
    

    for npc_object in npcs:
        # Add each NPC's collider to the collision checks
        collision_rects.append(npc_object.rect)
        # Update each NPC's state, providing the player's rect for collision detection
        npc_object.update(character.rect)



    # Existing logic for updating character
    character.update(keys, collision_rects, adjusted_dt, joystick)
    
    
    # Debugging: Check for collision with house colliders
    for house_collider in house_colliders:
        if character.rect.colliderect(house_collider):
            print(f"Character collided with house at {house_collider}")

    # Check for collision with the door collider and exit colliders
    # Now door_collider is accessible within this function
    # Check for collision with the door collider and exit colliders
    # Check for collision with the door collider and exit colliders
    # Check for collision with the door collider and exit colliders
    if door_collider and character.rect.colliderect(door_collider):
        print("Collided with door collider")
        print(f"door colliding with: {door_collider}")


    new_tmx_map = None
    new_destination = None

    # Ensure source_map is correctly set to the current map
    source_map = game_state.get('current_sub_region', None)



    for exit_name, (collider, destination) in exit_destinations.items():
        if character.rect.colliderect(collider):
            print(f"Collided with {exit_name}, transitioning from {source_map} to {destination}")
            new_tmx_file_path = os.path.join('sprites', f'{destination}.tmx')
            new_tmx_map = load_tmx_map(new_tmx_file_path)
            new_destination = destination
            break



    # Only perform the following steps when there is an actual map transition
    if new_tmx_map:
        # Perform the transition to the new map
        print(f"Transitioning to new TMX map: {new_destination}")
        game_state['tmx_map'] = new_tmx_map
        game_state['current_sub_region'] = new_destination

        # Clear existing data for transition
        npcs.clear()
        house_colliders.clear()
        wild_grass_colliders.clear()
        exit_destinations.clear()

        current_subregion = new_destination

        # Reinitialize environment for the new map
        house_colliders, door_collider, chest1_position, wild_grass_colliders, exit_destinations, new_npcs = setup_environment(new_tmx_map, new_destination, subregion_to_exits)
        npcs.extend(new_npcs)

        print(f"new same npcs: {npcs}")
        print(f"new npcs: {new_npcs}")

        print(f"1New house colliders: {house_colliders}")
        print(f"1New door collider: {door_collider}")
        print(f"1New exit destinations: {exit_destinations}")

        # Update collision rects with the new environment
        collision_rects.clear()  # Clear existing collision rects
        collision_rects, chest1_collision_rect = create_collision_rects(house_colliders, door_collider, chest1_position)


        # Reload the environment for the new subregion
        print("Re-initializing colliders and exit destinations for new map.")
        house_colliders, door_collider, chest1_position, wild_grass_colliders, exit_destinations, npcs = setup_environment(new_tmx_map, new_destination, subregion_to_exits)

        print(f"2New house colliders: {house_colliders}")
        print(f"2New door collider: {door_collider}")
        print(f"2New exit destinations: {exit_destinations}")
        # Update collision rects with the new environment
        collision_rects, chest1_collision_rect = create_collision_rects(house_colliders, door_collider, chest1_position)

        # Determine the appropriate spawn location based on the exit used
        exit_to_spawn_mapping = {
            'ExitNorth': 'SpawnSouth',
            'ExitSouth': 'SpawnNorth',
            'ExitEast': 'SpawnWest',
            'ExitWest': 'SpawnEast'
        }

        spawn_group_name = exit_to_spawn_mapping.get(exit_name, "SpawnNorth")  # Default spawn location

        spawn_position = None
        if hasattr(new_tmx_map, 'objectgroups'):
            for obj_group in new_tmx_map.objectgroups:
                if obj_group.name.lower() == "spawnspot":
                    for obj in obj_group:
                        if obj.name.lower() == spawn_group_name.lower():
                            spawn_position = (obj.x, obj.y)
                            break
                        if spawn_position:
                            break
        print(f"3New house colliders: {house_colliders}")
        print(f"3New door collider: {door_collider}")
        print(f"3New exit destinations: {exit_destinations}")

        if spawn_position:
            character.position = spawn_position
            character.rect.topleft = character.position
            


    # Reset mouse_up flag at the end of each update cycle
    mouse_up = False
    # Return new_tmx_map for checking in the main loop
    return new_tmx_map, new_destination

def create_collision_rects(house_colliders, door_collider, chest1_position):
    collision_rects = []

    # Initialize chest1_collision_rect to None
    chest1_collision_rect = None

    # Add each house and door collider to the collision rects
    collision_rects.extend(house_colliders)
    if door_collider:
        collision_rects.append(door_collider)

    # Add a collision rect for chest1 and store it separately
    if chest1_position:
        chest1_collision_rect = pygame.Rect(chest1_position[0], chest1_position[1], 16, 16)
        collision_rects.append(chest1_collision_rect)

    return collision_rects, chest1_collision_rect

def render_game(screen, tmx_map, character, npcs, interaction_rect):
    # First, render everything to a temporary surface
    temp_surface = pygame.Surface(screen.get_size())
    temp_surface.fill((0, 0, 0))  # Clear the temp surface
    render_map(temp_surface, tmx_map)  # Render the TMX map onto the temp surface
    character.draw(temp_surface)  # Draw the character onto the temp surface

    # Calculate the rectangle area around the player for the zoom effect
    zoom_rect_width, zoom_rect_height = 640, 480
    zoom_rect = pygame.Rect(
        character.position[0] - zoom_rect_width // 2, 
        character.position[1] - zoom_rect_height // 2, 
        zoom_rect_width, 
        zoom_rect_height
    )

    # Clamp the rectangle to ensure it doesn't go outside the map boundaries
    zoom_rect.clamp_ip(temp_surface.get_rect())

    # Update NPCs and check for interactions
    in_range_npc = False
    for npc in npcs:
        npc.update(character.rect)
        # Draw NPCs onto the temp surface
        npc.draw(temp_surface)
        # Check for collision with the interaction rect (adjusted for zoom)
        zoomed_interaction_rect = interaction_rect.move(-zoom_rect.left, -zoom_rect.top)
        if zoomed_interaction_rect.colliderect(npc.rect):
            in_range_npc = True

    # Capture the portion of the temp surface
    captured_area = temp_surface.subsurface(zoom_rect)

    # Scale this captured area to a larger size for the zoom effect
    zoom_scale = 2  # Adjust this value to control the zoom level
    zoomed_area = pygame.transform.scale(captured_area, (zoom_rect_width * zoom_scale, zoom_rect_height * zoom_scale))

    # Now, clear the main screen and blit the zoomed area onto it
    screen.fill((0, 0, 0))  # Clear the main screen
    screen.blit(zoomed_area, (0, 0))  # Blit the zoomed area onto the main screen

    # Draw a purple rectangle around the zoomed area on the main screen
    purple = (128, 0, 128)  # RGB for purple
    pygame.draw.rect(screen, purple, (0, 0, zoom_rect_width * zoom_scale, zoom_rect_height * zoom_scale), 2)

    # Update the display
    pygame.display.flip()
    return in_range_npc  # Return the flag indicating if player is in range of an NPC

def process_events():
    global running, mouse_up
    for event in pygame.event.get():
        if event.type == pygame.QUIT:
            running = False
        elif event.type == pygame.MOUSEBUTTONUP:
            mouse_up = True  # Set mouse_up to True when the mouse button is released


def explore(screen, human_trainer, items, trainers, pokemons, game_state, moves_dict):
    global item_taken, running

    # Load resources and initialize
    resources = explore_load_resources()
    mask_colliders = setup_collision_detection(resources['mask'])

    # Load the TMX map and current subregion
    tmx_map, current_subregion = load_subregion_map(game_state)

    # Setup the game environment
    house_colliders, door_collider, chest1_position, wild_grass_colliders, exit_destinations, npcs = setup_environment(tmx_map, current_subregion, subregion_to_exits)

    # Initialize the character
    character = Character(resources['character'], (48, 48), 6, 10)
    saved_position = game_state.get('saved_character_position', [screen.get_width() // 2 - character.sprite_size[0] // 2, screen.get_height() // 2 - character.sprite_size[1] // 2])
    character.position = saved_position
    character.rect.topleft = character.position

    # Create collision rects
    collision_rects, chest1_collision_rect = create_collision_rects(house_colliders, door_collider, chest1_position)

    # Main game loop
    running = True
    clock = pygame.time.Clock()
    while running:
        dt = clock.tick(60) / 1000
        keys = pygame.key.get_pressed()
        mouse_pos = pygame.mouse.get_pos()

        # Process game events
        process_events()

        # Handle input events
        interaction_rect = pygame.Rect(character.position[0] - 10, character.position[1] - 10, character.sprite_size[0] + 20, character.sprite_size[1] + 20)
        in_range_npc = handle_input_and_events(character, game_state, keys, door_collider, pre_battle_menu_pygame, screen, trainers, pokemons, chest1_collision_rect, location_items, npcs, moves_dict, interaction_rect)

        # Update game state
        new_tmx_map, new_destination = update_game_state(character, collision_rects, mask_colliders, dt, resources, encounter_probability, game_state, keys, wild_grass_colliders, exit_destinations, house_colliders, door_collider, chest1_collision_rect, npcs, None, None)

        # Render the game
        in_range_npc = render_game(screen, tmx_map, character, npcs, interaction_rect)

        # Reset mouse_up flag after updating the button
        mouse_up = False

        # Update the display
        pygame.display.flip()

    # Update the game state before returning
    game_state['human_trainer'] = human_trainer
    return game_state"""

def explore_and_return(screen, human_trainer, items, trainers, pokemons, game_state, moves_dict):
    updated_game_state = explore(screen, human_trainer, items, trainers, pokemons, game_state, moves_dict)
    # Rest of the code...

    # Check if human_trainer is in updated_game_state, if not, keep the original
    if 'human_trainer' not in updated_game_state:
        updated_game_state['human_trainer'] = game_state.get('human_trainer')

    # Update the global game state
    game_state.update(updated_game_state)

    # Return to the pre-battle menu with the updated game state
    pre_battle_menu_pygame(screen, game_state, game_state['human_trainer'])

def return_to_pre_battle_menu(screen, updated_game_state):
    human_trainer = updated_game_state.get('human_trainer')
    if human_trainer:
        pre_battle_menu_pygame(screen, updated_game_state, human_trainer)
    else:
        print("Error: human_trainer not found in updated_game_state")

"""def explore(screen, human_trainer, items, trainers, pokemons, game_state):
    # Define the base path for the sprites folder
    base_sprites_path = os.path.join(os.path.dirname(__file__), 'sprites')

    # Update paths to use relative paths
    paths = {
        'grass_tile': os.path.join(base_sprites_path, 'tilesets', 'grass.png'),
        'character': os.path.join(base_sprites_path, 'characters', 'player.png'),
        'mask': os.path.join(base_sprites_path, 'mapmask1.png'),
        'fence_sheet': os.path.join(base_sprites_path, 'tilesets', 'fences.png'),
        'high_grass_sheet': os.path.join(base_sprites_path, 'tilesets', 'highgrass.png'),
        'tall_grass_sheet': os.path.join(base_sprites_path, 'tilesets', 'wildgrass.png'),
        'chest_sheet': os.path.join(base_sprites_path, 'objects', 'chest_01.png')
    }

    # Load images using the updated relative paths
    grass_tile = pygame.transform.scale(pygame.image.load(paths['grass_tile']), 
                                        (pygame.image.load(paths['grass_tile']).get_width(), 
                                         pygame.image.load(paths['grass_tile']).get_height()))
    character = Character(paths['character'], (48, 48), 6, 10)
    mask_image = pygame.image.load(paths['mask']).convert_alpha()
    fence_sheet = pygame.image.load(paths['fence_sheet'])
    high_grass_sheet = pygame.image.load(paths['high_grass_sheet'])
    tall_grass_sheet = pygame.image.load(paths['tall_grass_sheet'])
    chest_sheet = pygame.image.load(paths['chest_sheet'])

    screen_width, screen_height = screen.get_size()
    tile_width, tile_height = grass_tile.get_size()

    # Window boundaries
    window_rect = pygame.Rect(0, 0, screen_width, screen_height)
    clock = pygame.time.Clock()

    # Character positioning
    saved_position = game_state.get('saved_character_position', 
                                    [screen_width // 2 - character.sprite_size[0] // 2, 
                                     screen_height // 2 - character.sprite_size[1] // 2])
    character.position = saved_position
    character.rect.topleft = character.position

    # Collision detection setup
    mask_colliders = [pygame.Rect(x, y, 1, 1) 
                      for x in range(mask_image.get_width()) 
                      for y in range(mask_image.get_height()) 
                      if mask_image.get_at((x, y)) != pygame.Color('black')]

    def can_move_to(mask, x, y, width, height):
        for dx in [0, width - 1]:
            for dy in [0, height - 1]:
                if mask.get_at((x + dx, y + dy)) != pygame.Color('black'):
                    return False
        return True

    # Load the fence sprite sheet
    #fence_sheet_path = 'F:/Scripts/PokePyMain-main/sprites/tilesets/fences.png'
    #fence_sheet_path = 'C:/Users/matth/OneDrive/PokePy/PokePyMain-main/sprites/tilesets/fences.png'
    #fence_sheet = pygame.image.load(fence_sheet_path)
    fence_tile_size = (16, 16)  # Each tile is 16x16 pixels

    # Function to get a specific tile from the fence sheet
    def get_fence_tile(col, row):
        return fence_sheet.subsurface(pygame.Rect(col * fence_tile_size[0], row * fence_tile_size[1], fence_tile_size[0], fence_tile_size[1]))

    # Define the layout of your initial fence tiles
    fence_positions = [
        # Example: (x_position, y_position, column_in_sheet, row_in_sheet)
        (100, 100, 0, 0),  # A1 fence tile at (100, 100)
        (100, 116, 0, 1),  # A2 fence tile at (100, 116)
        # ... add other initial fence positions if needed ...
    ]

    # Extend the fence vertically
    fence_length = 50  # Number of fence tiles
    fence_start_y = 100
    for i in range(fence_length):
        fence_positions.append((100, fence_start_y + i * 16, 0, 1))  # A2 fence tiles

    # Define padding for collision detection (smaller values for tighter collision)
    collision_padding = 1  # Example padding value

    # Create collision rectangles for each fence tile with reduced padding
    fence_collision_rects = []
    for x, y, _, _ in fence_positions:
        # Adjust the position and size of the collision rectangle based on the padding
        adjusted_rect = pygame.Rect(
            x + collision_padding, y + collision_padding,
            fence_tile_size[0] - 2 * collision_padding, fence_tile_size[1] - 2 * collision_padding
        )
        fence_collision_rects.append(adjusted_rect)

    # Load the high grass sprite sheet
    #high_grass_sheet_path = 'F:/Scripts/PokePyMain-main/sprites/tilesets/highgrass.png'
    #high_grass_sheet_path = 'C:/Users/matth/OneDrive/PokePy/PokePyMain-main/sprites/tilesets/highgrass.png'
    #high_grass_sheet = pygame.image.load(high_grass_sheet_path)
    high_grass_tile_size = (16, 16)  # Each tile is 8x8 pixels

    # Function to get a specific tile from the high grass sheet
    def get_high_grass_tile(col, row):
        return high_grass_sheet.subsurface(pygame.Rect(col * high_grass_tile_size[0], row * high_grass_tile_size[1], high_grass_tile_size[0], high_grass_tile_size[1]))

    # Define the layout of your high grass tiles
    high_grass_positions = [
        # Example: (x_position, y_position, column_in_sheet, row_in_sheet)
        (150, 150, 0, 0),  # A1 high grass tile at (150, 150)
        (150, 166, 0, 1),  # A2 high grass tile at (150, 158)
        (150, 182, 0, 1),  
        (150, 198, 0, 2),  
        # ... add other high grass positions if needed ...
    ]



    # Load the tall grass sprite sheet
    #tall_grass_sheet_path = 'F:/Scripts/PokePyMain-main/sprites/tilesets/wildgrass.png'
    #tall_grass_sheet_path = 'C:/Users/matth/OneDrive/PokePy/PokePyMain-main/sprites/tilesets/wildgrass.png'
    #tall_grass_sheet = pygame.image.load(tall_grass_sheet_path)
    tall_grass_tile_size = (16, 16)  # Assuming each tile is 16x16 pixels

    # Function to get a specific tile from the tall grass sheet
    def get_tall_grass_tile(col, row):
        return tall_grass_sheet.subsurface(pygame.Rect(col * tall_grass_tile_size[0], row * tall_grass_tile_size[1], tall_grass_tile_size[0], tall_grass_tile_size[1]))

    # Define the tall grass area
    tall_grass_area = pygame.Rect(300, 300, 100, 100)  # Adjust size and position as needed


    # Define the layout of your tall grass patches
    tall_grass_positions = [
        # Format: (x_position, y_position, column_in_sheet, row_in_sheet)
        # Add as many positions as you want for tall grass patches
        (300, 300, 0, 0),  # Example tall grass tile at (300, 300)

        # ... add more positions for additional patches ...
    ]

    # Load the chest sprite sheet and define chest tile size
    #chest_sheet_path = 'F:/Scripts/PokePyMain-main/sprites/objects/chest_01.png'
    #chest_sheet_path = 'C:/Users/matth/OneDrive/PokePy/PokePyMain-main/sprites/objects/chest_01.png'
    #chest_sheet = pygame.image.load(chest_sheet_path)
    chest_tile_size = (16, 16) 

    # Function to get a specific tile from the chest sheet
    def get_chest_tile(col):
        return chest_sheet.subsurface(pygame.Rect(col * chest_tile_size[0], 0, chest_tile_size[0], chest_tile_size[1]))

    # Define the position of the closed chest
    chest_position = (200, 600)
    closed_chest1_tile = get_chest_tile(0)  # A1 is chest1 closed

    # Create a collision rectangle for the chest
    chest_collision_rect = pygame.Rect(chest_position[0], chest_position[1], chest_tile_size[0], chest_tile_size[1])

    # Combine fence and chest collision rectangles
    collision_rects = fence_collision_rects + [chest_collision_rect]

    
    # Draw the high grass square and receive its collider
    high_grass_collider = draw_high_grass_square(screen, 500, 500, 25, 5, get_high_grass_tile)

    # Add the high grass collider to your list of collision rectangles
    collision_rects.append(high_grass_collider)



    # Initialize inventory in the game state if not present
    if 'inventory' not in game_state:
        game_state['inventory'] = []

    # Flag to track if the chest is open and item is taken
    chest_open = False
    item_taken = False


    
    # Initialize mouse position and mouse_up flag
    mouse_pos = (0, 0)  # Default mouse position
    mouse_up = False

        # Create an exit button
    exit_button = Button(1000, screen_height - 150, 200, 100, text="EXIT", 
                         function=return_to_pre_battle_menu, params=[screen, game_state])

    encounter_probability = 0.1  # Set this to desired probability (10% in this case)

    running = True
    while running:
        dt = clock.tick(60) / 1000  # Calculate delta time and convert milliseconds to seconds

        # Get the current mouse position
        mouse_pos = pygame.mouse.get_pos()  # Update mouse position here
        # Tiling the scaled background
        for y in range(0, screen_height, tile_height):
            for x in range(0, screen_width, tile_width):
                screen.blit(grass_tile, (x, y))

        keys = pygame.key.get_pressed()
        character.update(keys, collision_rects + mask_colliders, dt, tall_grass_area)

        # Check for wild Pokémon encounter
        # Check for wild Pokémon encounter
        if character.check_for_wild_pokemon_encounter(tall_grass_area) and random.random() < encounter_probability:
            # Save the current position before the battle
            game_state['saved_character_position'] = character.position.copy()

            # Trigger the wild Pokémon battle
            print("A wild Pokémon appears in Kanto, Pallet Town!")
            chosen_region = "Kanto"
            chosen_sub_region = "Pallet Town"
            human_trainer.battle_wild_pokemon(chosen_region, chosen_sub_region, pokemons, game_state)

            # Restore the character's position after the battle
            character.position = saved_position
            character.rect.topleft = character.position

            # Optionally, break out of the loop to end exploration after the battle
            # break


        # Check if the new position is within the window boundaries
        if not window_rect.contains(character.rect):
            # If the move is not allowed, revert the character's position
            character.position = original_position
        else:
            # Check if the new position is allowed using the mask
            try:
                if not can_move_to(mask_image, character.position[0], character.position[1], character.sprite_size[0], character.sprite_size[1]):
                    # If the move is not allowed, revert the character's position
                    character.position = original_position
            except IndexError:
                # If we're checking a position outside the mask, revert the position
                character.position = original_position


        # Draw each fence tile at the specified positions
        for x, y, col, row in fence_positions:
            fence_tile = get_fence_tile(col, row)
            screen.blit(fence_tile, (x, y))

        # Draw each high grass tile at the specified positions
        for x, y, col, row in high_grass_positions:
            high_grass_tile = get_high_grass_tile(col, row)
            screen.blit(high_grass_tile, (x, y))


        # Reset mouse_up flag at the beginning of each loop iteration
        mouse_up = False

        # Inside the game loop
        # Inside the game loop
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                # Save the character's position before quitting
                game_state['saved_character_position'] = character.position.copy()
                running = False
            elif event.type == pygame.KEYDOWN:
                if event.key == pygame.K_RETURN:
                    interaction_rect = pygame.Rect(
                        character.position[0] - 10, character.position[1] - 10,
                        character.sprite_size[0] + 20, character.sprite_size[1] + 20
                    )

                    if interaction_rect.colliderect(chest_collision_rect) and not item_taken:
                        chest_open = True
                        # Find the Potion item from the items list and make a deep copy
                        item = copy.deepcopy(items.get('Potion'))
                        if item:  # Check if the Potion item exists
                            human_trainer.add_item(item)  # Add potion to the human_trainer's items
                            item_taken = True
                            print("You found a Potion!")
                            print("Trainer's Items:", human_trainer.items)
                        else:
                            print("Potion not found in items list")

            # Detect mouse button up event for button click
            elif event.type == pygame.MOUSEBUTTONUP:
                mouse_pos = pygame.mouse.get_pos()
                mouse_up = True  # Set mouse_up to True when the mouse button is released
            else:
                mouse_up = False  # Ensure mouse_up is False at other times

        # Update and draw the exit button
        exit_button.update(mouse_pos, mouse_up)
        exit_button.draw(screen)




        keys = pygame.key.get_pressed()
        #character.update(keys, collision_rects)  # Update character with collision detection



        draw_high_grass_square(screen, 500, 500, 25, 5, get_high_grass_tile)
        # Draw the tall grass patches on the screen
        draw_tall_grass_area(screen, tall_grass_area, get_tall_grass_tile)

        # When checking for collision, also check against the mask colliders
        original_position = character.position.copy()
        character.update(keys, collision_rects + mask_colliders, dt, tall_grass_area)  # Include tall grass area in the update call # Now also checking against mask colliders Include delta time in movement calculations

        character.draw(screen)

        # Draw the chest, open or closed based on the flag
        chest_tile = get_chest_tile(2 if chest_open else 0)  # C1 is chest1 open, A1 is chest1 closed
        screen.blit(chest_tile, chest_position)

        pygame.display.flip()  # Update the screen with the new background
        pygame.time.Clock().tick(60)  # 60 frames per second
            # Return the updated game state when the loop ends
    
    # At the end of the function, before returning the updated game_state
    game_state['human_trainer'] = human_trainer  # Update the human_trainer in the game state

    return game_state"""



def scan_menu_wrapper(screen, human_trainer, items, trainers, pokemons, game_state, moves):
    # Pass pokemons and moves to the scan menu
    scan_menu_pygame(screen, pokemons, moves, game_state, human_trainer)

def create_scan_menu_buttons(screen, screen_width, screen_height, pokemons, moves, game_state, human_trainer):
    button_width, button_height = 400, 100
    button_spacing = 20
    total_button_height = 2 * button_height + button_spacing
    start_y = (screen_height - total_button_height) / 2

    # Call read_function when the read button is pressed
    read_btn = Button((screen_width - button_width) / 2, start_y, button_width, button_height, "READ", function=scan_read_menu_pygame, params=[screen, pokemons, moves, game_state, human_trainer])
    
    write_btn = Button((screen_width - button_width) / 2, start_y + button_height + button_spacing, button_width, button_height, "WRITE", function=scan_write_menu_pygame, params=[screen, pokemons, moves, game_state, human_trainer])
    back_btn = Button((screen_width - button_width) / 2, start_y + 2 * (button_height + button_spacing), button_width, button_height, "BACK", function=pre_battle_menu_pygame, params=[screen, game_state, human_trainer])

    return [read_btn, write_btn, back_btn]

def render_scan_menu(screen, bg_image, gif_images, current_frame_original, gif_images_middle, current_frame_middle, gif_images_top, current_frame_top, buttons):
    screen.blit(bg_image, (0, 0))

    # Display the GIF animations
    screen.blit(gif_images[current_frame_original], (800, 600))
    screen.blit(gif_images_middle[current_frame_middle], (0, 0))  # Centered middle gif
    screen.blit(gif_images_top[current_frame_top], (0, 0))

    for button in buttons:
        button.draw(screen)

    pygame.display.flip()

def scan_menu_pygame(screen, pokemons, moves, game_state, human_trainer):
    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
    frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0


    window_width, window_height = screen.get_size()
    buttons = create_scan_menu_buttons(screen, window_width, window_height, pokemons, moves, game_state, human_trainer)
    # Rest of your existing code
    selected_button_index = 0
    using_keyboard = False

    running = True
    while running:
        running, using_keyboard, selected_button_index, mouse_up = handle_events(buttons, using_keyboard, selected_button_index)

        for button in buttons:
            button.update(pygame.mouse.get_pos(), mouse_up, keyboard_navigation=using_keyboard)

        # Update the GIF animations
        frame_counter_original += 1
        frame_counter_middle += 1
        frame_counter_top += 1

        if frame_counter_original % 10 == 0:
            current_frame_original = (current_frame_original + 1) % len(gif_images)
        if frame_counter_middle % 10 == 0:
            current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        if frame_counter_top % 10 == 0:
            current_frame_top = (current_frame_top + 1) % len(gif_images_top)

        render_scan_menu(screen, bg_image, gif_images, current_frame_original, gif_images_middle, current_frame_middle, gif_images_top, current_frame_top, buttons)

        pygame.time.Clock().tick(60)

    pygame.quit()

def create_scan_write_menu_buttons(screen, screen_width, screen_height, game_state, human_trainer):
    button_width, button_height = 400, 100
    start_y = 760

    write_btn = Button((screen_width - button_width) / 2, start_y, button_width, button_height, "WRITE", function=write_function, params=[screen])

    # Ensure that game_state and human_trainer are passed correctly
    back_btn = Button((screen_width - button_width) / 2, start_y + button_height + 20, button_width, button_height, "BACK", function=pre_battle_menu_pygame, params=[screen, game_state, human_trainer])

    return [write_btn, back_btn]

# Adjust render_scan_write_menu to display multiple labels
def render_scan_write_menu(screen, bg_image, gif_images, current_frame_original, gif_images_middle, current_frame_middle, gif_images_top, current_frame_top, buttons, pokemon_labels):
    screen.blit(bg_image, (0, 0))

    # Display the GIF animations
    screen.blit(gif_images[current_frame_original], (800, 600))
    screen.blit(gif_images_middle[current_frame_middle], (0, 0))
    screen.blit(gif_images_top[current_frame_top], (0, 0))

    # Display Pokémon attributes if there are any labels
    if pokemon_labels:  # Check if pokemon_labels list is not empty
        label_start_y = 100  # Starting position for the first label
        label_spacing = 40   # Space between labels
        for i, label in enumerate(pokemon_labels):
            screen.blit(label, (400, label_start_y + i * label_spacing))

    for button in buttons:
        button.draw(screen)

    pygame.display.flip()

def scan_write_menu_pygame(screen, pokemons, moves, game_state, human_trainer):
    global scanned_pokemon_data

    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
    frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0


    window_width, window_height = screen.get_size()
    # Now passing the correct parameters to create_scan_write_menu_buttons
    buttons = create_scan_write_menu_buttons(screen, window_width, window_height, game_state, human_trainer)


    # Select a random Pokémon, create a deep copy and adjust its attributes
    random_pokemon_key = random.choice(list(pokemons.keys()))
    random_pokemon = pokemons[random_pokemon_key]
    pokemon_copy = copy.deepcopy(random_pokemon)

    # Generate a level using a normal distribution centered around 30
    level = max(1, min(100, int(np.random.normal(loc=30, scale=7))))
    pokemon_copy.level = level

    # Adjust stats based on level and randomness
    pokemon_copy.max_health = int(pokemon_copy.max_health * (level / 30) * random.uniform(0.8, 1.2))
    pokemon_copy.attack = int(pokemon_copy.attack * (level / 30) * random.uniform(0.8, 1.2))
    pokemon_copy.defense = int(pokemon_copy.defense * (level / 30) * random.uniform(0.8, 1.2))
    pokemon_copy.speed = int(pokemon_copy.speed * (level / 30) * random.uniform(0.8, 1.2))
    pokemon_copy.current_health = pokemon_copy.max_health

    # Adjust price based on level (if applicable)
    # Note: Uncomment and adjust if price attribute exists
    # pokemon_copy.price *= level

    # Get the last 4 moves that the Pokémon can learn at its current level
    pokemon_copy.moves = PokemonFactory.get_moves_at_level(pokemon_copy.moves_to_learn, pokemon_copy.level, moves)

    # Update scanned_pokemon_data with the details of pokemon_copy
    scanned_pokemon_data = {
        "name": pokemon_copy.name,
        "level": pokemon_copy.level,
        "max_health": pokemon_copy.max_health,
        "attack": pokemon_copy.attack,
        "defense": pokemon_copy.defense,
        "speed": pokemon_copy.speed,
        "current_health": pokemon_copy.current_health,
        # Add other relevant details
        "moves": [move.name for move in pokemon_copy.moves[:4]]  # Assuming moves is a list of Move objects
    }

    # Debugging: Print the data that will be written
    print("Scanned Pokémon data to write:", scanned_pokemon_data)


    # Create labels for displaying Pokémon attributes
    font = pygame.font.Font(None, 36)
    pokemon_labels = [
        font.render(f"Name: {pokemon_copy.name}", True, (255, 255, 255)),
        font.render(f"Level: {pokemon_copy.level}", True, (255, 255, 255)),
        font.render(f"Health: {pokemon_copy.current_health}/{pokemon_copy.max_health}", True, (255, 255, 255)),
        font.render(f"Attack: {pokemon_copy.attack}", True, (255, 255, 255)),
        font.render(f"Defense: {pokemon_copy.defense}", True, (255, 255, 255)),
        font.render(f"Speed: {pokemon_copy.speed}", True, (255, 255, 255)),
        # Add more attributes if needed
    ]

    # Display moves (limited to 4 for simplicity)
    for i, move in enumerate(pokemon_copy.moves[:4]):
        pokemon_labels.append(font.render(f"Move {i + 1}: {move.name}", True, (255, 255, 255)))

    selected_button_index = 0
    using_keyboard = False

    running = True
    while running:
        running, using_keyboard, selected_button_index, mouse_up = handle_events(buttons, using_keyboard, selected_button_index)

        for button in buttons:
            button.update(pygame.mouse.get_pos(), mouse_up, keyboard_navigation=using_keyboard)

        frame_counter_original += 1
        frame_counter_middle += 1
        frame_counter_top += 1

        if frame_counter_original % 10 == 0:
            current_frame_original = (current_frame_original + 1) % len(gif_images)
        if frame_counter_middle % 10 == 0:
            current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        if frame_counter_top % 10 == 0:
            current_frame_top = (current_frame_top + 1) % len(gif_images_top)

        render_scan_write_menu(screen, bg_image, gif_images, current_frame_original, gif_images_middle, current_frame_middle, gif_images_top, current_frame_top, buttons, pokemon_labels)

        pygame.time.Clock().tick(60)

    pygame.quit()

def scan_read_menu_pygame(screen, pokemons, moves, game_state, human_trainer):
    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()
    window_width, window_height = screen.get_size()

    # Buttons for reading from RFID and going back
    read_btn = Button((window_width - 400) / 2, 200, 400, 100, "READ", function=read_function, params=[screen])
    back_btn = Button((window_width - 400) / 2, 350, 400, 100, "BACK", function=pre_battle_menu_pygame, params=[screen, game_state, human_trainer])

    running = True
    while running:
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            elif event.type == pygame.MOUSEBUTTONDOWN:
                if read_btn.is_over(pygame.mouse.get_pos()):
                    read_btn.function(*read_btn.params)
                if back_btn.is_over(pygame.mouse.get_pos()):
                    back_btn.function(*back_btn.params)

        screen.blit(bg_image, (0, 0))

        # Update and draw buttons
        mouse_pos = pygame.mouse.get_pos()
        read_btn.update(mouse_pos, False, keyboard_navigation=False)
        back_btn.update(mouse_pos, False, keyboard_navigation=False)
        read_btn.draw(screen)
        back_btn.draw(screen)

        pygame.display.flip()
        pygame.time.Clock().tick(60)

    pygame.quit()

def condense_pokemon_data(pokemon_data):
    # Only extract and return the name of the Pokémon
    return pokemon_data.get("name", "")


def display_read_data(screen, pokemon_data):
    bg_image, _, _, _ = load_resources()  # Reusing the background image
    font = pygame.font.Font(None, 36)
    window_width, window_height = screen.get_size()

    # Create a back button
    back_btn = Button(50, window_height - 150, 200, 50, "BACK", function=scan_menu_pygame, params=[screen, None, None, None, None, None, None])

    running = True
    while running:
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            elif event.type == pygame.MOUSEBUTTONUP:
                if back_btn.is_over(pygame.mouse.get_pos()):
                    running = False

        screen.blit(bg_image, (0, 0))
        y_position = 100

        # Iterate through the pokemon_data dictionary and display each item
        # Iterate through the pokemon_data dictionary and display each item
        pokemon_name = pokemon_data.get("name", "Unknown")
        text = font.render(f"Name: {pokemon_name}", True, (255, 255, 255))
        screen.blit(text, (100, 100))

        # Draw the back button
        back_btn.update(pygame.mouse.get_pos(), False, keyboard_navigation=False)
        back_btn.draw(screen)

        pygame.display.flip()
        pygame.time.Clock().tick(60)

# Function to detect the ACR122U reader
def detect_reader():
    r = readers()
    for reader in r:
        if 'ACR122' in reader.name:
            return reader
    return None

def get_reader_connection():
    reader = detect_reader()
    if reader is not None:
        connection = reader.createConnection()
        connection.connect()
        return connection
    else:
        raise Exception("No RFID reader found")

def read_function(screen):
    try:
        conn = get_reader_connection()
        start_block_to_read = 4
        num_blocks_to_read = 2  # Adjust based on your data size
        card_data = read_long_data_from_card(conn, start_block_to_read, num_blocks_to_read)
        pokemon_data = parse_condensed_pokemon_data(card_data)
        print("Read Pokémon name:", pokemon_data.get("name", "Unknown"))
        display_read_data(screen, pokemon_data)
    except Exception as e:
        print(f"Error in read_function: {e}")

def parse_condensed_pokemon_data(data_str):
    parts = data_str.split(',')
    if len(parts) < 7:  # Adjust this number based on the expected minimum number of elements
        return {"Error": "Incomplete data"}
    pokemon_data = {
        "name": parts[0],
        "level": parts[1],
        "max_health": parts[2],
        "attack": parts[3],
        "defense": parts[4],
        "speed": parts[5],
        "moves": parts[6:]
    }
    return pokemon_data

# Function to read data from a specific block of the RFID card
def read_from_card(connection, block):
    # Key type A (0x60) or B (0x61) - change according to your key
    KEY_TYPE = 0x60
    # Default key
    KEY = [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]
    # Block number to read from
    BLOCK_NUMBER = block

    # Authentication command - replace with your key and block number
    load_key_command = [0xFF, 0x82, 0x00, 0x00, 0x06] + KEY
    authenticate_command = [0xFF, 0x86, 0x00, 0x00, 0x05, 0x01, 0x00, BLOCK_NUMBER, KEY_TYPE, 0x00]

    # Load authentication keys
    load_key_response, sw1, sw2 = connection.transmit(load_key_command)
    if sw1 != 0x90 or sw2 != 0x00:
        return f"Load Key Error: SW1: {sw1}, SW2: {sw2}"

    # Authenticate
    auth_response, sw1, sw2 = connection.transmit(authenticate_command)
    if sw1 != 0x90 or sw2 != 0x00:
        return f"Authentication Error: SW1: {sw1}, SW2: {sw2}"

    # Read command
    read_command = [0xFF, 0xB0, 0x00, BLOCK_NUMBER, 0x10]
    read_response, sw1, sw2 = connection.transmit(read_command)
    if sw1 == 0x90 and sw2 == 0x00:
        # Convert byte array back to string, assuming ASCII encoding
        return ''.join(chr(i) for i in read_response if i != 0x00)
    else:
        return f"Read Error: SW1: {sw1}, SW2: {sw2}"

def read_long_data_from_card(connection, start_block, num_blocks):
    full_data = ''
    for block in range(start_block, start_block + num_blocks):
        block_data = read_from_card(connection, block)
        if "Error" in block_data:
            return block_data
        full_data += block_data

    # Return the concatenated string up to the first null character
    return full_data.split('\x00', 1)[0]

def write_function(screen):
    global scanned_pokemon_data
    try:
        conn = get_reader_connection()
        start_block = 4
        condensed_data = condense_pokemon_data(scanned_pokemon_data)
        if condensed_data:
            print("Data to write:", condensed_data)  # Debug statement
            write_response = write_long_data_to_card(conn, start_block, condensed_data)
            print("Write response:", write_response)  # Debug statement
        else:
            print("Error: Condensed data is empty")
    except Exception as e:
        print(f"Error in write_function: {e}")

# Rest of the functions from your reference code remain unchanged

def write_to_card(connection, block, data_str):
    # Convert string to byte array and pad or trim to fit the block size
    data = [ord(c) for c in data_str.ljust(16, '\x00')][:16]

    # Key type A (0x60) or B (0x61) - change according to your key
    KEY_TYPE = 0x60
    KEY = [0xFF, 0xFF, 0xFF, 0xFF, 0xFF, 0xFF]
    BLOCK_NUMBER = block

    load_key_command = [0xFF, 0x82, 0x00, 0x00, 0x06] + KEY
    authenticate_command = [0xFF, 0x86, 0x00, 0x00, 0x05, 0x01, 0x00, BLOCK_NUMBER, KEY_TYPE, 0x00]

    # Load authentication keys and authenticate
    load_key_response, sw1, sw2 = connection.transmit(load_key_command)
    if sw1 != 0x90 or sw2 != 0x00:
        return f"Load Key Error: SW1: {sw1}, SW2: {sw2}"

    auth_response, sw1, sw2 = connection.transmit(authenticate_command)
    if sw1 != 0x90 or sw2 != 0x00:
        return f"Authentication Error: SW1: {sw1}, SW2: {sw2}"

    # Write command
    write_command = [0xFF, 0xD6, 0x00, BLOCK_NUMBER, 0x10] + data
    write_response, sw1, sw2 = connection.transmit(write_command)
    if sw1 == 0x90 and sw2 == 0x00:
        return "Write Successful"
    else:
        return f"Write Error: SW1: {sw1}, SW2: {sw2}"

def parse_condensed_pokemon_data(data_str):
    # Since we are only storing and reading the name, the entire string is the Pokémon name
    return {"name": data_str}

# Ensure to implement or adjust condense_pokemon_data() based on your data structure.

def write_long_data_to_card(connection, start_block, data_str):
    # Split the data into 16-byte chunks
    chunks = [data_str[i:i+16] for i in range(0, len(data_str), 16)]

    for i, chunk in enumerate(chunks):
        response = write_to_card(connection, start_block + i, chunk)
        if "Successful" not in response:
            return f"Error writing to block {start_block + i}: {response}"

    return "Write Successful"





def load_resources():
    # Load background image as before
    bg_image = pygame.image.load('pokemon_arena.jpg')
    bg_image = pygame.transform.scale(bg_image, (1280, 920))

    try:
        # Attempt to load and process the GIF frames
        gif_frames = extract_and_save_gif_frames('anim_leaves.gif', 'frames')
        gif_images = [pygame.image.load(frame) for frame in gif_frames]
        gif_images_middle = [pygame.transform.scale(image, (image.get_width()*3, image.get_height()*3)) for image in gif_images]
        gif_images_top = [pygame.transform.flip(image, True, True) for image in gif_images[::-1]]
    except PermissionError:
        # Handle the PermissionError by using empty lists for GIF images
        print("Permission denied for loading GIF frames. Skipping GIF images.")
        gif_images, gif_images_middle, gif_images_top = [], [], []

    return bg_image, gif_images, gif_images_middle, gif_images_top

def create_pre_battle_menu_buttons(screen, screen_width, screen_height, game_state, human_trainer, trainers, moves, pokemons, items):
    button_width, button_height = 400, 100
    button_spacing = 20
    total_button_height = (6 * button_height) + (5 * button_spacing)  # Adjust for additional SCAN button
    start_y = (screen_height - total_button_height) / 2

    battle_btn = Button((screen_width - button_width) / 2, start_y, button_width, button_height, "BATTLE", function=choose_battle_menu_pygame, params=[screen, game_state, human_trainer, trainers, moves, pokemons])
    manage_btn = Button((screen_width - button_width) / 2, start_y + button_height + button_spacing, button_width, button_height, "MANAGE", function=manage_menu_pygame, params=[screen, human_trainer, items, trainers, pokemons, game_state])
    # Update the explore_btn to include moves_dict in its parameters
    explore_btn = Button((screen_width - button_width) / 2, start_y + 2 * (button_height + button_spacing), 
                         button_width, button_height, "EXPLORE", 
                         function=explore_and_return, 
                         params=[screen, human_trainer, items, trainers, pokemons, game_state, moves])

    # In the create_pre_battle_menu_buttons function
    # In the pre_battle_menu_pygame function or similar
    scan_btn = Button((screen_width - button_width) / 2, start_y + 3 * (button_height + button_spacing), button_width, button_height, "SCAN", function=scan_menu_wrapper, params=[screen, human_trainer, items, trainers, pokemons, game_state, moves])
    options_btn = Button((screen_width - button_width) / 2, start_y + 4 * (button_height + button_spacing), button_width, button_height, "OPTIONS", function=options_menu_pygame, params=[screen, game_state, human_trainer])
    exit_btn = Button((screen_width - button_width) / 2, start_y + 5 * (button_height + button_spacing), button_width, button_height, "EXIT", function=exit_game)

    return [battle_btn, manage_btn, explore_btn, scan_btn, options_btn, exit_btn]  # Include the new SCAN button

def handle_events(buttons, using_keyboard, selected_button_index):
    mouse_up = False
    for event in pygame.event.get():
        if event.type == pygame.QUIT:
            return False, using_keyboard, selected_button_index, mouse_up
        if event.type == pygame.MOUSEBUTTONUP:
            mouse_up = True
            if using_keyboard:
                using_keyboard = False
        if event.type == pygame.KEYDOWN:
            using_keyboard = True
            if event.key == pygame.K_DOWN:
                selected_button_index = (selected_button_index + 1) % len(buttons)
            elif event.key == pygame.K_UP:
                selected_button_index = (selected_button_index - 1) % len(buttons)
            elif event.key == pygame.K_RETURN:
                buttons[selected_button_index].clicked = True
                if buttons[selected_button_index].function:
                    if buttons[selected_button_index].params:
                        buttons[selected_button_index].function(*buttons[selected_button_index].params)
                    else:
                        buttons[selected_button_index].function()

    return True, using_keyboard, selected_button_index, mouse_up

def render_screen(screen, bg_image, gif_images, current_frame_original, gif_images_middle, current_frame_middle, gif_images_top, current_frame_top, buttons, using_keyboard, mouse_up):
    screen.blit(bg_image, (0, 0))
    
    # Check if gif_images is not empty before blitting
    if gif_images:
        screen.blit(gif_images[current_frame_original], (800, 600))
    
    # Check if gif_images_middle is not empty before blitting
    if gif_images_middle:
        screen.blit(gif_images_middle[current_frame_middle], (0, 0))  # Centered middle gif
    
    # Check if gif_images_top is not empty before blitting
    if gif_images_top:
        screen.blit(gif_images_top[current_frame_top], (0, 0))

    for button in buttons:
        button.update(pygame.mouse.get_pos(), mouse_up, keyboard_navigation=using_keyboard)
        button.draw(screen)

    pygame.display.flip()
    pygame.time.Clock().tick(60)

def pre_battle_menu_pygame(screen, game_state, human_trainer):
    trainers = game_state['trainers']
    pokemons = game_state['pokemons']
    items = game_state['items']
    moves = game_state['moves']

    print(human_trainer.items)

    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()
    
    # Check if gif_images is not empty before initializing frame counters
    if gif_images:
        current_frame_original = 0
        frame_counter_original = 0
    else:
        current_frame_original = None
        frame_counter_original = None

    if gif_images_middle:
        current_frame_middle = len(gif_images_middle) // 3
        frame_counter_middle = 0
    else:
        current_frame_middle = None
        frame_counter_middle = None

    if gif_images_top:
        current_frame_top = 2 * len(gif_images_top) // 3
        frame_counter_top = 0
    else:
        current_frame_top = None
        frame_counter_top = None

    window_width, window_height = screen.get_size()
    buttons = create_pre_battle_menu_buttons(screen, window_width, window_height, game_state, human_trainer, trainers, moves, pokemons, items)
    selected_button_index = 0
    using_keyboard = False

    running = True
    while running:
        running, using_keyboard, selected_button_index, mouse_up = handle_events(buttons, using_keyboard, selected_button_index)
        
        # Update GIF frames only if the lists are not empty
        if gif_images and frame_counter_original is not None:
            frame_counter_original += 1
            if frame_counter_original % 2 == 0:
                current_frame_original = (current_frame_original + 1) % len(gif_images)

        if gif_images_middle and frame_counter_middle is not None:
            frame_counter_middle += 1
            if frame_counter_middle % 2 == 0:
                current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)

        if gif_images_top and frame_counter_top is not None:
            frame_counter_top += 1
            if frame_counter_top % 2 == 0:
                current_frame_top = (current_frame_top + 1) % len(gif_images_top)

        # Highlight the currently selected button
        for i, button in enumerate(buttons):
            if i == selected_button_index:
                button.highlighted = True
            else:
                button.highlighted = False

        render_screen(screen, bg_image, gif_images, current_frame_original, gif_images_middle, current_frame_middle, gif_images_top, current_frame_top, buttons, using_keyboard, mouse_up)

    pygame.quit()




"""def choose_battle_menu_pygame(screen, game_state, human_trainer, trainers, moves, pokemons):
    # Create buttons for different battle options
    y_pos = 100
    y_increment = 60

    font = pygame.font.Font(font_path, 24)

    choose_trainer_btn = Button(300, y_pos, 200, 50, "CHOOSE", function=choose_trainer_to_battle_pygame, params=[screen, game_state, human_trainer, trainers, moves])
    battle_random_btn = Button(300, y_pos + y_increment, 200, 50, "RANDOM", function=battle_random_trainer_pygame, params=[human_trainer, trainers, moves, screen, game_state])
    battle_by_region_btn = Button(300, y_pos + y_increment * 2, 200, 50, "REGION", function=battle_trainers_by_region_menu, params=[screen, human_trainer, trainers, moves, game_state])
    battle_by_team_btn = Button(300, y_pos + y_increment * 3, 200, 50, "TEAM", function=battle_trainers_by_team_menu, params=[screen, human_trainer, trainers, moves, game_state])
    battle_wild_pokemon_btn = Button(275, y_pos + y_increment * 5, 250, 50, "WILD POKEMON", function=battle_wild_pokemon_menu_pygame, params=[human_trainer, pokemons, game_state, screen, font])

    back_btn = Button(300, y_pos + y_increment * 7, 200, 50, "BACK", function=pre_battle_menu_pygame, params=[screen, game_state, human_trainer])

    buttons = [choose_trainer_btn, battle_random_btn, battle_wild_pokemon_btn, battle_by_team_btn, battle_by_region_btn, back_btn]

    # Battle Menu loop
    running = True
    while running:
        mouse_up = False
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            if event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True

        screen.fill((255, 255, 255))  # Fill the screen with white color

        # Update and draw buttons
        for button in buttons:
            button.update(pygame.mouse.get_pos(), mouse_up)
            button.draw(screen)

        pygame.display.flip()  # Update the display

        pygame.time.Clock().tick(60)  # Limit the frame rate to 60 FPS
"""

def create_battle_choice_buttons(screen, screen_width, screen_height, game_state, human_trainer, trainers, moves, pokemons):
    # Initialize the font here or pass it as a parameter to this function
    font = pygame.font.SysFont(None, 36)
    
    button_width, button_height = 400, 100
    button_spacing = 20
    total_button_height = (5 * button_height) + (4 * button_spacing)
    start_y = (screen_height - total_button_height) / 2

    choose_trainer_btn = Button((screen_width - button_width) / 2, start_y, button_width, button_height, "CHOOSE", function=choose_trainer_to_battle_pygame, params=[screen, game_state, human_trainer, trainers, moves])
    battle_random_btn = Button((screen_width - button_width) / 2, start_y + button_height + button_spacing, button_width, button_height, "RANDOM", function=battle_random_trainer_pygame, params=[human_trainer, trainers, moves, screen, game_state])
    battle_by_region_btn = Button((screen_width - button_width) / 2, start_y + 2 * (button_height + button_spacing), button_width, button_height, "REGION", function=battle_trainers_by_region_menu, params=[screen, human_trainer, trainers, moves, game_state])
    battle_by_team_btn = Button((screen_width - button_width) / 2, start_y + 3 * (button_height + button_spacing), button_width, button_height, "TEAM", function=battle_trainers_by_team_menu, params=[screen, human_trainer, trainers, moves, game_state])
    battle_wild_pokemon_btn = Button((screen_width - button_width) / 2, start_y + 4 * (button_height + button_spacing), button_width, button_height, "WILD", function=battle_wild_pokemon_menu_pygame, params=[human_trainer, pokemons, game_state, screen, font])
    back_btn = Button((screen_width - button_width) / 2, start_y + 5 * (button_height + button_spacing), button_width, button_height, "BACK", function=pre_battle_menu_pygame, params=[screen, game_state, human_trainer])
    
    return [choose_trainer_btn, battle_random_btn, battle_by_region_btn, battle_by_team_btn, battle_wild_pokemon_btn, back_btn]

def choose_battle_menu_pygame(screen, game_state, human_trainer, trainers, moves, pokemons):
    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()

    # Initialize the frame counters and frame update counters
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
    frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0

    window_width, window_height = screen.get_size()
    buttons = create_battle_choice_buttons(screen, window_width, window_height, game_state, human_trainer, trainers, moves, pokemons)
    selected_button_index = 0
    using_keyboard = False

    running = True
    while running:
        running, using_keyboard, selected_button_index, mouse_up = handle_events(buttons, using_keyboard, selected_button_index)
        
        # Update GIF frames every 10 refreshes
        frame_counter_original += 1
        frame_counter_middle += 1
        frame_counter_top += 1
        
        if frame_counter_original % 2 == 0:
            current_frame_original = (current_frame_original + 1) % len(gif_images)
        if frame_counter_middle % 2 == 0:
            current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        if frame_counter_top % 2 == 0:
            current_frame_top = (current_frame_top + 1) % len(gif_images_top)
        
        # Highlight the currently selected button
        for i, button in enumerate(buttons):
            if i == selected_button_index:
                button.highlighted = True
            else:
                button.highlighted = False

        render_screen(screen, bg_image, gif_images, current_frame_original, gif_images_middle, current_frame_middle, gif_images_top, current_frame_top, buttons, using_keyboard, mouse_up)

    pygame.quit()



# Global variable to store the currently selected item and a flag for item selection
current_selected_item = None
item_selected_flag = False  # New flag to check if an item has been selected

def use_item_pygame(screen, human_trainer, items, game_state):
    # Load resources
    bg_image = pygame.image.load('pokemon_arena.jpg')
    bg_image = pygame.transform.scale(bg_image, (1280, 920))
    font = pygame.font.Font(None, 32)

    # Define the function to display the Pokémon team
    """def display_pokemon_team():
        y = 20
        for pokemon in human_trainer.pokemon_list:
            text = f"{pokemon.name}: {pokemon.current_health}/{pokemon.max_health}"
            label = font.render(text, True, (0, 0, 0))
            screen.blit(label, (20, y))
            y += 40"""


    # Modify the use_item function to set the current_selected_item
    # Modify the use_item function to set the current_selected_item
    def use_item(item_object):
        global current_selected_item, item_selected_flag
        current_selected_item = item_object
        item_selected_flag = True  # Set the flag when an item is selected
        print(f"Item selected: {item_object.name}")

    # Function to handle item usage on a Pokémon
    # Function to handle item usage on a Pokémon
    def select_pokemon_for_item(pokemon):
        global current_selected_item, item_selected_flag
        if current_selected_item is not None and item_selected_flag:
            print(f"Selected Pokemon for item use: {pokemon.name}")  # Debug: Confirm Pokemon selection
            apply_item_effect(pokemon, current_selected_item)
            decrement_item_quantity(current_selected_item)
            current_selected_item = None
            item_selected_flag = False  # Reset the flag after applying the item


    # Function to apply the item effect
    # Function to apply the item effect
    # Function to apply the item effect
    def apply_item_effect(pokemon, item):
        print(f"Applying item effect: {item.name} to {pokemon.name}")
        if item.name == "Potion":
            print(f"Applying Potion to {pokemon.name}")
            if 'heal' in item.effect:
                heal_amount = item.effect['heal']  # Assuming 'heal' effect is a dictionary key
                print(f"Pokemon's health before healing: {pokemon.current_health}")
                pokemon.heal(heal_amount)
                print(f"Pokemon's health after healing: {pokemon.current_health}")
            else:
                print("Potion does not have a 'heal' effect.")
        elif item.name == "Revive":
            # Similar logic for Revive if applicable
            pass
        else:
            print(f"Item {item.name} not recognized for effect application")


    # Function to decrement item quantity
    def decrement_item_quantity(item):
        for i, (itm, qty) in enumerate(human_trainer.items):
            if itm == item:
                human_trainer.items[i] = (itm, qty - 1)  # Decrement quantity
                if human_trainer.items[i][1] <= 0:
                    human_trainer.items.pop(i)  # Remove item if quantity is 0
                break

    # Modify the use_item function to set the current_selected_item
    """def use_item(item_object):
        global current_selected_item
        current_selected_item = item_object
        if item_object.target == "choose_own_pokemon":
            create_pokemon_buttons()
        else:
            # Handle other item targets
            print(f"Using item: {item_object.name}")"""



    # Display inventory items with mouse hover detection
    # Function to display inventory items and handle button interactions
    # Function to display inventory items and handle button interactions
    # Function to display inventory items and handle button interactions
    def display_inventory_items(mouse_pos, mouse_up):
        y = 20
        item_buttons = []  # Store buttons to update their state later
        for item_pair in human_trainer.items:
            item_object = item_pair[0]  # Assuming the first element is the Item object
            quantity = item_pair[1]     # Assuming the second element is the quantity
            button_text = f"{item_object.name.upper()} : {quantity}"
            item_button = Button(440, y, 600, 100, button_text, function=use_item, params=[item_object])
            item_buttons.append(item_button)

            # Check if the mouse is hovering over the button and add white border
            if item_button.is_over(mouse_pos):
                item_button.highlighted = True  # Activate highlighting
            else:
                item_button.highlighted = False  # Deactivate highlighting

            item_button.draw(screen)
            y += 110

        # Update button state based on mouse position and handle click events
        for button in item_buttons:
            if button.update(mouse_pos, mouse_up):
                button.function(*button.params if button.params else [])
    
    # Global variable for the back button
    back_button = Button(20, 800, 200, 100, "BACK", color=(0, 128, 128), highlighted_color=(255, 255, 255))

    # Main game loop
    # Main game loop
    running = True
    while running:
        mouse_pos = pygame.mouse.get_pos()  # Get the current mouse position
        mouse_up = False  # Flag to track mouse button up event

        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            if event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True
                print("Mouse button released")  # Debug: Confirm mouse button release

        screen.blit(bg_image, (0, 0))
        #display_pokemon_team()

        if current_selected_item and item_selected_flag and current_selected_item.target == "choose_own_pokemon":
            y = 20
            for i, pokemon in enumerate(human_trainer.pokemon_list):
                button_text = f"{pokemon.name}: {pokemon.current_health}/{pokemon.max_health}"
                pokemon_button = Button(20, y, 600, 100, button_text.upper(), function=select_pokemon_for_item, params=[pokemon])
                pokemon_button.update(mouse_pos, mouse_up)
                pokemon_button.draw(screen)
                y += 110
                if mouse_up:
                    print(f"Checking button for {pokemon.name}")  # Debug: Check button interaction

        display_inventory_items(mouse_pos, mouse_up)
        
        # Handle Back Button
        # Handle Back Button
        back_button.update(mouse_pos, mouse_up)
        back_button.draw(screen)
        if back_button.clicked:
            game_state['human_trainer'] = human_trainer  # Update the game_state with the current state of human_trainer
            running = False  # Exit loop if back button is clicked


        pygame.display.flip()
        pygame.time.Clock().tick(60)

    # Return the updated game state
    return game_state



def manage_menu_pygame(screen, human_trainer, items, trainers, pokemons, game_state):
    # Use the same bg_image, gif_frames, gif_images, etc.
    bg_image = pygame.image.load('pokemon_arena.jpg')
    bg_image = pygame.transform.scale(bg_image, (1280, 920))

    # GIF setup
    gif_frames = extract_and_save_gif_frames('anim_leaves.gif', 'frames')
    gif_images = [pygame.image.load(frame) for frame in gif_frames]
    gif_images_middle = [pygame.transform.scale(image, (image.get_width()*3, image.get_height()*3)) for image in gif_images]
    gif_images_top = [pygame.transform.flip(image, True, True) for image in gif_images[::-1]]

    current_frame_original = 0
    current_frame_middle = len(gif_images) // 3
    current_frame_top = 2 * len(gif_images) // 3
    frame_counter_original = 0
    frame_counter_middle = 0
    frame_counter_top = 0

    
    # Positioning for the buttons and pokemon list
    y_pos = 50  # Define the y_pos here
    y_increment = 75

    # Create Pokémon health messages outside the main loop
    pokemon_health_messages = [f"{pokemon.name.upper()}: {pokemon.current_health}/{pokemon.max_health}" for pokemon in human_trainer.pokemon_list]

    # Define the color and alpha for the teal background
    teal = (0, 128, 128)
    alpha = 192  # 75% opacity (192/255)

    # Calculate the position and size of the background rectangle
    bg_rect_margin = 20
    bg_rect_width = 500
    bg_rect_height = (len(pokemon_health_messages) * y_increment + 2 * y_increment + 2 * bg_rect_margin) - 150
    bg_rect_x = 100 - bg_rect_margin
    
    # Updated position for the teal background to just enclose the Pokémon list
    bg_rect_y = 150  # Updated the y position

    # Create the teal background surface with white border
    bg_surface = pygame.Surface((bg_rect_width, bg_rect_height), pygame.SRCALPHA)
    
    # Round the corners by drawing four circles at each corner and filling the rest
    corner_radius = 20

    # First, draw the teal background
    pygame.draw.circle(bg_surface, teal + (alpha,), (corner_radius, corner_radius), corner_radius)  # Bottom-left corner
    pygame.draw.circle(bg_surface, teal + (alpha,), (bg_rect_width - corner_radius, corner_radius), corner_radius)  # Bottom-right corner
    pygame.draw.circle(bg_surface, teal + (alpha,), (corner_radius, bg_rect_height - corner_radius), corner_radius)  # Top-left corner
    pygame.draw.circle(bg_surface, teal + (alpha,), (bg_rect_width - corner_radius, bg_rect_height - corner_radius), corner_radius)  # Top-right corner
    pygame.draw.rect(bg_surface, teal + (alpha,), (corner_radius, 0, bg_rect_width - 2 * corner_radius, bg_rect_height))
    pygame.draw.rect(bg_surface, teal + (alpha,), (0, corner_radius, bg_rect_width, bg_rect_height - 2 * corner_radius))

    border_thickness = 18  # Define the thickness of the border, adjust as needed
    corner_border_thickness = 10

    # Now, draw the white borders and arcs on top of the teal background
    pygame.draw.line(bg_surface, (255, 255, 255), (corner_radius, 1), (bg_rect_width - corner_radius, 1), border_thickness)
    pygame.draw.line(bg_surface, (255, 255, 255), (corner_radius, bg_rect_height - 1), (bg_rect_width - corner_radius, bg_rect_height - 1), border_thickness)
    pygame.draw.line(bg_surface, (255, 255, 255), (1, corner_radius), (1, bg_rect_height - corner_radius), border_thickness)
    pygame.draw.line(bg_surface, (255, 255, 255), (bg_rect_width - 1, corner_radius), (bg_rect_width - 1, bg_rect_height - corner_radius), border_thickness)
    pygame.draw.arc(bg_surface, (255, 255, 255), (0, bg_rect_height - 2 * corner_radius, 2 * corner_radius, 2 * corner_radius), math.pi, 1.5 * math.pi, corner_border_thickness)
    pygame.draw.arc(bg_surface, (255, 255, 255), (bg_rect_width - 2 * corner_radius, bg_rect_height - 2 * corner_radius, 2 * corner_radius, 2 * corner_radius), 1.5 * math.pi, 2 * math.pi, corner_border_thickness)
    pygame.draw.arc(bg_surface, (255, 255, 255), (0, 0, 2 * corner_radius, 2 * corner_radius), 0.5 * math.pi, math.pi, corner_border_thickness)
    pygame.draw.arc(bg_surface, (255, 255, 255), (bg_rect_width - 2 * corner_radius, 0, 2 * corner_radius, 2 * corner_radius), 0, 0.5 * math.pi, corner_border_thickness)

    # Display trainer stats
    trainer_name = f"NAME: {human_trainer.name}"
    trainer_stats = f"COIN: {human_trainer.coins} HEALTH: {human_trainer.current_health} MANA: {human_trainer.mana}"
    font = pygame.font.Font(font_path, 24)

    # Create an empty list for buttons
    buttons = []


    window_width, window_height = screen.get_size()
    button_width, button_height = 400, 100
    button_spacing = 15

    # Adjust start_y for two rows
    start_y = window_height - 2 * (button_height + button_spacing)

    # Calculate starting x-coordinate for 3 buttons evenly spaced
    start_x = (window_width - 3 * button_width - 2 * button_spacing) / 2

    # Create and position the buttons for the first row
    visit_pokemart_btn = Button(start_x, start_y, button_width, button_height, "POKEMART", function=visit_pokemart_pygame, params=[screen, human_trainer, items, font, game_state])
    buttons.append(visit_pokemart_btn)

    access_storage_btn = Button(start_x + (button_width + button_spacing), start_y, button_width, button_height, "STORAGE", function=access_storage_pygame, params=[screen, human_trainer, trainers, pokemons, items, game_state])
    buttons.append(access_storage_btn)

    visit_pokecenter_btn = Button(start_x + 2 * (button_width + button_spacing), start_y, button_width, button_height, "POKECENTER", function=visit_pokecenter_pygame, params=[human_trainer, pre_battle_menu_pygame, screen, game_state, trainers, pokemons])
    buttons.append(visit_pokecenter_btn)

    # Create and position the buttons for the second row
    trade_btn = Button(start_x, start_y + button_height + button_spacing, button_width, button_height, "TRADE", function=trade_pokemon_select_trainer_pygame, params=[screen, human_trainer, trainers, game_state])
    buttons.append(trade_btn)


    # Position the back button in the middle of the second row
    back_btn = Button(start_x + (button_width + button_spacing), start_y + button_height + button_spacing, button_width, button_height, "BACK", function=pre_battle_menu_pygame, params=[screen, game_state, human_trainer])
    buttons.append(back_btn)

    
    # Create and position the "Use Item" button in the second row
    use_item_btn = Button(start_x + 2 * (button_width + button_spacing), start_y + button_height + button_spacing, button_width, button_height, "USE ITEM", function=use_item_pygame, params=[screen, human_trainer, items, game_state])
    buttons.append(use_item_btn)


    
    def get_pokemon_image_path(pokemon_name):
        """Return the path to the image for the given Pokémon."""
        pokemon_details = game_state['pokemons'].get(pokemon_name)  # Use game_state to access pokemons
        if not pokemon_details:
            raise ValueError(f"No Pokemon found with the name {pokemon_name}")

        try:
            pokemon_index = pokemon_details.index
            formatted_index = f"{pokemon_index:04}"  # Zero-pad the index to ensure it's 4 digits
        except ValueError:
            raise ValueError(f"No Pokemon found with the name {pokemon_name}")
                
        #return os.path.join("F:\\Scripts\\PokePyMain-main\\pokemon_pics", f"{formatted_index}{pokemon_name}.png")
        #return os.path.join("C:\\Users\\matth\\OneDrive\\PokePy\\PokePyMain-main\\pokemon_pics", f"{formatted_index}{pokemon_name}.png")
        #return os.path.join("C:\\Users\\Tusa\\OneDrive\\PokePy\\PokePyMain-main\\pokemon_pics", f"{formatted_index}{pokemon_name}.png")
    
        return os.path.join("pokemon_pics", f"{formatted_index}{pokemon_name}.png")
    


    selected_button_index = 0  # Index for the currently selected button
    using_keyboard = False  # Flag to determine if keyboard navigation is being used



    # Manage Menu loop
    running = True
    while running:
        # Refresh Pokémon health messages each time the loop runs
        pokemon_health_messages = [f"{pokemon.name.upper()}: {pokemon.current_health}/{pokemon.max_health}" 
                                   for pokemon in human_trainer.pokemon_list]
        
        mouse_up = False
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            if event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True
                using_keyboard = False  # Reset the keyboard flag when mouse is used
            if event.type == pygame.KEYDOWN:
                using_keyboard = True  # Set the flag for keyboard navigation
                if event.key == pygame.K_RIGHT:
                    # Move to the right, stop at the end of the row
                    if selected_button_index % 3 < 2:  # Ensure it's not already the rightmost button in the row
                        selected_button_index += 1

                elif event.key == pygame.K_LEFT:
                    # Move to the left, stop at the start of the row
                    if selected_button_index % 3 > 0:  # Ensure it's not already the leftmost button in the row
                        selected_button_index -= 1

                elif event.key == pygame.K_DOWN:
                    # Move down, wrap around if necessary
                    if selected_button_index + 3 < len(buttons):
                        selected_button_index += 3
                    else:
                        # Move to the same column in the first row
                        selected_button_index %= 3

                elif event.key == pygame.K_UP:
                    # Move up, wrap around if necessary
                    if selected_button_index - 3 >= 0:
                        selected_button_index -= 3
                    else:
                        # Move to the same column in the last row
                        last_row_start_index = len(buttons) - (len(buttons) % 3)
                        selected_button_index = last_row_start_index + (selected_button_index % 3)

                elif event.key == pygame.K_RETURN:
                    # Ensure bounds are respected
                    selected_button_index = max(0, min(selected_button_index, len(buttons) - 1))
                    # Execute the function associated with the currently selected button
                    selected_button = buttons[selected_button_index]
                    if selected_button.function:
                        if selected_button.params:
                            selected_button.function(*selected_button.params)
                        else:
                            selected_button.function()
                elif event.key == pygame.K_BACKSPACE:
                    # Trigger the back button
                    back_btn.clicked = True
                    if back_btn.function:
                        if back_btn.params:
                            back_btn.function(*back_btn.params)
                        else:
                            back_btn.function()

        # Update the highlight for buttons based on the selected_button_index
        for i, button in enumerate(buttons):
            if i == selected_button_index:
                button.highlighted = True
            else:
                button.highlighted = False

        # First, fill the screen with white color
        screen.fill((255, 255, 255))
        
        # Draw the background image
        screen.blit(bg_image, (0, 0))

        # Draw the teal background with a white border
        screen.blit(bg_surface, (bg_rect_x, bg_rect_y))

        # Render the GIFs
        screen.blit(gif_images[current_frame_original], (800, 600))
        screen.blit(gif_images_middle[current_frame_middle], (0, 0))
        screen.blit(gif_images_top[current_frame_top], (0, 0))

        # Update GIF frames
        frame_counter_original += 1
        frame_counter_middle += 1
        frame_counter_top += 1

        if frame_counter_original >= 2:
            current_frame_original = (current_frame_original + 1) % len(gif_images)
            frame_counter_original = 0
        if frame_counter_middle >= 2:
            current_frame_middle = (current_frame_middle + 1) % len(gif_images)
            frame_counter_middle = 0
        if frame_counter_top >= 2:
            current_frame_top = (current_frame_top + 1) % len(gif_images)
            frame_counter_top = 0
        # Display trainer stats with white color
        text_surface = font.render(trainer_name, True, (255, 255, 255))
        screen.blit(text_surface, (100, 20))
        text_surface = font.render(trainer_stats, True, (255, 255, 255))
        screen.blit(text_surface, (100, 50))

        # Adjust y_pos for Pokémon messages
        adjusted_y_pos = y_pos + len(trainer_stats.split('\n')) * y_increment

        # Blit Pokémon images and their health stats
        # Blit Pokémon images and their health stats
        for i, health_msg in enumerate(pokemon_health_messages):
            pokemon = human_trainer.pokemon_list[i]

            # Load and display the image of the Pokémon
            pokemon_image = pygame.image.load(get_pokemon_image_path(pokemon.name))
            scaled_pokemon_image = pygame.transform.scale(pokemon_image, (80, 80))

            # Position the Pokémon image to the left of the text
            image_position = (100, adjusted_y_pos + i * y_increment + 50)
            screen.blit(scaled_pokemon_image, image_position)

            # Adjust the position of the health message to the right of the image and render with white color
            text_position = (image_position[0] + scaled_pokemon_image.get_width() + 10, image_position[1])
            health_text = font.render(health_msg, True, (255, 255, 255))
            screen.blit(health_text, text_position)

        # Update and draw buttons
        for button in buttons:
            button.update(pygame.mouse.get_pos(), mouse_up, keyboard_navigation=using_keyboard)
            button.draw(screen)

        pygame.display.flip()  # Update the display

        pygame.time.Clock().tick(60)  # Limit the frame rate to 60 FPS

"""def options_menu_pygame(screen, game_state, human_trainer):
    # Extract required values from game_state
    trainers = game_state['trainers']
    pokemons = game_state['pokemons']
    items = game_state['items']
    tm_chart = game_state['tm_chart']
    spells_chart = game_state['spells_chart']
    moves = game_state['moves']
    # Create buttons for options
    y_pos = 100
    y_increment = 60

    start_new_game_btn = Button(300, y_pos, 200, 50, "NEW GAME", function=start_new_game_window, params=[trainers, pokemons, items, tm_chart, spells_chart, moves])
    save_game_btn = Button(300, y_pos + y_increment, 200, 50, "SAVE GAME", function=save_game_pygame, params=[screen, game_state, human_trainer])
    load_game_btn = Button(300, y_pos + y_increment * 2, 200, 50, "LOAD GAME", function=load_game_pygame, params=[screen, game_state])
    delete_game_btn = Button(300, y_pos + y_increment * 3, 200, 50, "DELETE GAME", function=delete_saved_game_pygame, params=[screen])

    back_btn = Button(300, y_pos + y_increment * 4, 200, 50, "Back", function=pre_battle_menu_pygame, params=[screen, game_state, human_trainer])

    buttons = [start_new_game_btn, save_game_btn, load_game_btn, delete_game_btn, back_btn]

    # Options Menu loop
    running = True
    while running:
        mouse_up = False
        for event in pygame.event.get():
            if event.type == pygame.QUIT:
                running = False
            if event.type == pygame.MOUSEBUTTONUP:
                mouse_up = True

        screen.fill((255, 255, 255))  # Fill the screen with white color

        # Update and draw buttons
        for button in buttons:
            button.update(pygame.mouse.get_pos(), mouse_up)
            button.draw(screen)

        pygame.display.flip()  # Update the display

        pygame.time.Clock().tick(60)  # Limit the frame rate to 60 FPS
"""

def options_menu_pygame(screen, game_state, human_trainer):
    # Extract required values from game_state
    trainers = game_state['trainers']
    pokemons = game_state['pokemons']
    items = game_state['items']
    tm_chart = game_state['tm_chart']
    spells_chart = game_state['spells_chart']
    moves = game_state['moves']

    bg_image, gif_images, gif_images_middle, gif_images_top = load_resources()
    
    # Create buttons for options
    window_width, window_height = screen.get_size()

    #print(f"window height: {window_height}")
    
    button_width = 500
    button_height = 100
    y_increment = 120  # Increased to accommodate for the larger button height
    y_pos = (window_height - (4 * y_increment)) // 2

    print(f"y pos: {y_pos}")

    x_pos = (window_width - button_width) // 2  # Centered x position

    start_new_game_btn = Button(x_pos, y_pos, button_width, button_height, "NEW GAME", function=start_new_game_window, params=[trainers, pokemons, items, tm_chart, spells_chart, moves])
    save_game_btn = Button(x_pos, y_pos + y_increment, button_width, button_height, "SAVE GAME", function=save_game_pygame, params=[screen, game_state, human_trainer])
    load_game_btn = Button(x_pos, y_pos + 2 * y_increment, button_width, button_height, "LOAD GAME", function=load_game_pygame, params=[screen, game_state])
    delete_game_btn = Button(x_pos, y_pos + 3 * y_increment, button_width, button_height, "DELETE GAME", function=delete_saved_game_pygame, params=[screen, game_state])
    back_btn = Button(x_pos, y_pos + 4 * y_increment, button_width, button_height, "BACK", function=pre_battle_menu_pygame, params=[screen, game_state, human_trainer])

    buttons = [start_new_game_btn, save_game_btn, load_game_btn, delete_game_btn, back_btn]
    
    # Initialize the frame counters and frame update counters
    current_frame_original, current_frame_middle, current_frame_top = 0, len(gif_images) // 3, 2 * len(gif_images) // 3
    frame_counter_original, frame_counter_middle, frame_counter_top = 0, 0, 0
    selected_button_index = 0
    using_keyboard = False

    running = True
    while running:
        running, using_keyboard, selected_button_index, mouse_up = handle_events(buttons, using_keyboard, selected_button_index)
        
        # Update GIF frames every 10 refreshes
        frame_counter_original += 1
        frame_counter_middle += 1
        frame_counter_top += 1
        
        if frame_counter_original % 2 == 0:
            current_frame_original = (current_frame_original + 1) % len(gif_images)
        if frame_counter_middle % 2 == 0:
            current_frame_middle = (current_frame_middle + 1) % len(gif_images_middle)
        if frame_counter_top % 2 == 0:
            current_frame_top = (current_frame_top + 1) % len(gif_images_top)
        
        # Highlight the currently selected button
        for i, button in enumerate(buttons):
            if i == selected_button_index:
                button.highlighted = True
            else:
                button.highlighted = False

        render_screen(screen, bg_image, gif_images, current_frame_original, gif_images_middle, current_frame_middle, gif_images_top, current_frame_top, buttons, using_keyboard, mouse_up)

    pygame.quit()

def exit_game():
    pygame.quit()
    sys.exit()

#initialize_game()
initialize_pygame()